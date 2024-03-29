{-# LANGUAGE TemplateHaskell, TupleSections, GeneralizedNewtypeDeriving, ScopedTypeVariables, DeriveGeneric, TypeSynonymInstances, FlexibleInstances, ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module ProcessExpr where

import Control.Arrow ( second, (***) )
import Control.Applicative ( (<$>) )
import Control.DeepSeq ( NFData(..) )
import Control.Lens ( makeLenses, (%=), use, (.=) )
import Control.Monad ( when, liftM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State.Strict ( StateT, runStateT, modify
                                        , get, runState )
import Data.Hashable ( Hashable(..) )
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Maybe ( fromMaybe, listToMaybe )
import qualified Data.Map.Strict as M ( lookup, empty, insert, size )
import Data.Map.Strict ( Map )
import qualified Data.Set as S
import Data.Traversable ( traverse )
import DSL.Expr ( Expr(..), Value(..), BinOp(..), VarId(varToInt)
                , InterleavingMarkedNet, reassocExpr )
import GHC.Generics ( Generic )
import Marking ( concatMarkingList )
import Minimisation ( minimise )
import LTS ( statesLTS )
import NFA ( NFAWithBoundaries(..), tensor, modifyNFAWB, compose
           , toNFAWithMarking, equivalenceHKC, epsilonCloseNFA, NFA(..)
           , reflexivelyCloseNFA, nfaReachability )
import Nets ( composeMarkedNet, tensor, MarkedNet )
import Util ( promptForParam, ReachabilityResult(..), ReassocResult(..), decideVerifiability )
import Data.IORef ( newIORef )
import Debug.Trace

data WithId a = WithId a Int

unWithId :: WithId a -> (a, Int)
unWithId (WithId a i) = (a, i)

instance (NFData a) => NFData (WithId a) where
    rnf (WithId a i) = rnf a `seq` rnf i

instance Eq (WithId a) where
    (WithId _ x) == (WithId _ y) = x == y

type NFAWithBounds = NFAWithBoundaries Int

-- Newtype that encapsulates equality on language, not structure of NFAWBs. We
-- tag each NFA with a unique id, to increase performance where identical NFAs
-- are repeatedly generated.
newtype NFALang = NFALang { unNFALang :: WithId NFAWithBounds }
                deriving NFData

instance Show NFALang where
    show (NFALang (unWithId -> (a, _))) = show a

instance Hashable NFALang where
    -- Use the unique id as the (unique) hashcode
    hashWithSalt s (NFALang (WithId _ nfaId)) = hashWithSalt s nfaId

-- important function that is indeirectly used for the fixed-point checking
instance Eq NFALang where
    (NFALang (unWithId -> (NFAWithBoundaries nfa1 l1 r1, id1)))
        == (NFALang (unWithId -> (NFAWithBoundaries nfa2 l2 r2, id2)))
            = id1 == id2 || (l1 == l2 && r1 == r2 && equivalenceHKC nfa1 nfa2)

toRawNFA :: NFALang -> NFAWithBounds
toRawNFA = fst . unWithId . unNFALang

data OpType = Tensor
            | Compose
            deriving (Eq, Ord, Generic)

instance NFData OpType

instance Hashable OpType

type OpTriple = (NFALang, NFALang, OpType)

type Net2NFAMap = Map MarkedNet NFALang
type NFABinaryMap = HashMap OpTriple NFALang

data StrictTriple = StrictTriple
                        { _st1 :: !Int
                        , _st2 :: !Int
                        , _st3 :: !Int
                        } deriving Show

instance NFData StrictTriple

$(makeLenses ''StrictTriple)

data StrictQuad = StrictQuad
                      { _sq1 :: !Int
                      , _sq2 :: !Int
                      , _sq3 :: !Int
                      , _sq4 :: !Int
                      } deriving Show

instance NFData StrictQuad

$(makeLenses ''StrictQuad)

data Counters = Counters
    { -- toNFA known, library known, neither
      _leafC :: !StrictTriple
      -- compose known, compose unknown, tensor known, tensor unknown
    , _binOpC :: !StrictQuad
    }

instance NFData Counters where
    rnf (Counters l b) = rnf l `seq` rnf b `seq` ()

instance Show Counters where
    show (Counters leaf bin) = show (leaf, bin)

$(makeLenses ''Counters)

-- We use 3 memoisation maps to improve performance: the first is used to avoid
-- state explosion, while the other two prevent us doing repeated work:
--     1. NFA: a "library" of seen NFAs stored in reduced form, which are
--        checked against using language equivalence, returning the existing
--        reduced NFA if we match language.
--     2. (Net, NFA): we only convert Nets once.
--     3. (NFA, NFA, Op, NFA) only perform the binary operation on NFAs once
-- also keep the fixed-point in case one is reached

data MemoState = MemoState
    { _counters :: !Counters
    , _knownNFAs :: !(Int, [NFALang])
    , _net2NFA :: !Net2NFAMap
    , _binOpMap :: !NFABinaryMap
    , _fpcounter :: !(Maybe Int)
    }

$(makeLenses ''MemoState)

type Sizes = (Int, Int, Int)
type NFAEvalM = StateT MemoState IO


exprEval :: forall r m . (Monad m, Eq r, Show r)
         -- A function that'll turn nets into an "r" (whatever r ends up being)
         => (InterleavingMarkedNet -> m r)
         -- A function to handle the sequential composition of two `r`s to produce a (monad-action producing a) value
         -> (r -> r -> m (Value m r))
         -- A function to handle the tensor composition of two `r`s to produce a (monad-action producing a) value
         -> (r -> r -> m (Value m r))
         -- Function to set the fixed point status
         -> (Int -> m ())
         -- Function to set the parameter status
         -- -> (Int -> m ())
         -- A monadic "action" that'll produce an int (probably easiest to ignore this for now)
         -> (m Int)
         -- The expression we're evaluating 
         -- return a monad action (where the monad is `m`) that produces the "value" that is the result of the evaluation
         -> Expr r -> m (Value m r)
exprEval onConstant onSeq onTens onFP getP expr = eval expr []
  where
    evalToBase e env = do
        res <- eval e env
        case res of
            VBase p -> return p
            VInt i -> error $ "Finished evaluation with int: " ++ show i
            VLam _ -> error "Finished evaluation with function type!"

    evalToInt e env = do
        res <- eval e env
        case res of
            VInt i -> return i
            _ -> error "Finished evaluation with non-int type!"

    eval :: Expr r -> [Value m r] -> m (Value m r)
    -- Handle the Net cases
    eval (ENum n) _ = return (VInt n)
    eval ERead _ = do 
        param <- getP
        return (VInt param)     
    eval (EBin op x y) env = do
        let f = case op of
                    Add -> (+)
                    Sub -> (-)
        x' <- evalToInt x env
        y' <- evalToInt y env
        return $ VInt $ x' `f` y'
    eval (EIntCase i z s) env = do
        i' <- evalToInt i env
        -- evaluate either the zero or the (succ i) case
        case i' of
            0 -> eval z env
            nonzero
                | nonzero > 0 ->
                    eval (EApp s (EIntCase (ENum $ nonzero - 1) z s)) env
                | otherwise -> error "Detected negative intcase argument!"
    eval (EStarCase i z s n) env = do
        offset <- eval n env
        resPair <- foldWFP i z s env offset
        return (snd resPair)
    eval (EPreComputed pc) _ = return (VBase pc)
    eval (EConstant constant) _ = liftM VBase $ onConstant constant
    eval (ESeq t1 t2) env = doRecurse t1 t2 env onSeq
    eval (ETen t1 t2) env = doRecurse t1 t2 env onTens
    -- Handle the ML-like cases
    eval (EVar v) env = return $ env !! varToInt v
    eval (EApp e1 e2) env = do
        f <- eval e1 env
        v <- eval e2 env
        case f of
            (VLam f') -> f' v
            _ -> error "Attempting to apply non-lambda"
    eval (ELam body) env = return $ VLam (\arg -> eval body (arg : env))
    eval (EBind e1 body) env = do
        -- To allow recursive bindings, use this
        -- arg <- mfix (\x -> eval e1 (x : env))
        arg <- eval e1 env
        eval body (arg : env)

    -- eval :: Expr r -> [Value m r] -> m (Value m r)
    --foldWFP :: Expr r -> Expr r -> Expr r -> [Value m r]
    --   -> m (Bool, Value m r)     
    -- main fixed-point detection algorithm
    -- used during evaluation of EStarCase    
    foldWFP n term f env fpOffset = do
        i' <- evalToInt n env
        -- evaluate either the zero or the (succ i) case
        case i' of
            0 -> do
                baseRes <- eval term env
                -- put the pair in the m monad 
                return (True, baseRes)
            nonzero
                | nonzero > 0 -> do
                    --resPair <- trace ("Calling fold with: " ++ show i') (foldWFP (ENum (nonzero - 1)) term f env fpOffset)
                    resPair <- (foldWFP (ENum (nonzero - 1)) term f env fpOffset)
                    let res = snd resPair
                        resExpr = fromValue res 
                        exec = fst resPair in -- tells whether to compose with term 
                        case exec of 
                            True -> do
                                app <- eval (EApp f (EPreComputed resExpr)) env
                                -- this is the check for weak-language equivalence 
                                -- internally it uses the NFALang and its comparison defined above
                                if app == res  
                                    then do 
                                        onFP . offsetFixedPoint i' $ fromValueInt fpOffset
                                        -- return fixed-point net and tell say to not keep composing
                                        return (False, app) 
                                    else 
                                        -- fixed-point not reached so the recursion keeps looking
                                        return (True, app)
                            False -> do
                                -- in case fixed-point has been reached don't compose and just return it
                                return resPair
                | otherwise -> error "Detected negative intcase argument!"
    
    doRecurse :: Expr r -> Expr r -> [Value m r] -> (r -> r -> m (Value m r))
              -> m (Value m r)
    doRecurse expr1 expr2 env doCompose = do
        res1 <- evalToBase expr1 env
        res2 <- evalToBase expr2 env
        doCompose res1 res2

    --fromValue :: Value m r -> r
    fromValue (VBase p) = p
    fromValue _ = error "Non-base type" 

    -- the fixed-point number depends on whether the expression is starcase or **
    -- this function is used by the optimisation to kow where to begin checking from again
    -- ofsetting is used to set the fixed-point as number of nets that are composed
    offsetFixedPoint :: Int -> Int -> Int
    offsetFixedPoint n 0 = n
    offsetFixedPoint 1 1 = 1
    offsetFixedPoint n 1 = n - 1
    offsetFixedPoint _ _ = error "Error in offsetting the fixed point"

    -- used for the offsetting
    fromValueInt (VInt p) = p
    fromValueInt _ = error "Non-int type" 

newtype MaxComp = MaxComp (Integer, (Integer, Integer))
                deriving Show

instance Eq MaxComp where
    (MaxComp (t1, _)) == (MaxComp (t2, _)) = t1 == t2

instance Ord MaxComp where
    compare (MaxComp (t1, _)) (MaxComp (t2, _)) = compare t1 t2

instance NFData MaxComp where
    rnf (MaxComp d) = rnf d


expr2NFAWFP :: IO Int -> Expr NFAWithBounds
         -> IO (ReachabilityResult, ReassocResult)
expr2NFAWFP getP expr = do
    param <- getP
    reachRes <- makeProof expr param Nothing True
    case reachRes of 
        (FPVerifiable _) -> return (reachRes, ReassocNotAttempted)
        _            -> do
            let assocExpr = reassocExpr expr
            case assocExpr of 
                (nexpr, ReassocApplied a) -> do
                    reachRes' <- makeProof nexpr param Nothing True
                    return (reachRes', ReassocApplied a)
                (_, ReassocFail)        -> return (reachRes, ReassocFail)
                _                       -> return (reachRes, ReassocFail) -- this is ReassocNotAttempted and cant happen
  where
    -- the main function that verifies reachability for the system
    makeProof expr' n fp maxIter =  do
        ref <- newIORef (fromMaybe [] (Just [n]))
        let (numberedExpr, nfas) =
                runState (traverse initialNumbering expr') (0, [])
            initState = MemoState initCounters nfas M.empty HM.empty Nothing
            -- getP' = trace ("Calling makeProof with " ++ (show n)) (promptForParam ref)
            getP' = promptForParam ref
        case n of 
            1 -> do 
                evalRes <- second getCountAndSizes <$> runStateT (doEval numberedExpr getP') initState
                let nfa = nfaReachability $ fst evalRes
                    (_, _, fpres) = snd evalRes
                case (nfa, fp, fpres) of 
                    (True, Just p, _) -> return (FPVerifiable p)
                    (True, _, Just p) -> return (FPVerifiable p) -- the case where 1 is the limit set by the user
                    (True, _, _)      -> return (FPUnreachable 1)
                    (False, _, _)     -> return (decideVerifiability 1 fp fpres)
            _ -> do
                evalRes <- second getCountAndSizes <$> runStateT (doEval numberedExpr getP') initState
                let nfa = nfaReachability $ fst evalRes
                    (_, _, fpres) = snd evalRes
                case (maxIter, nfa, fpres) of 
                    (True, _, Nothing) -> return (FPUnreachable n)
                    (_, False, _)      -> return (decideVerifiability n fp fpres)
                    (_, _, Just p)     -> makeProof expr' p (Just p) False
                    _                  -> makeProof expr' (n - 1) fp False

    initialNumbering = getOrInsert (return ()) (return ()) get modify

    doEval numberedExpr getP' = do
        res <- exprEval onNet onSeq onTens onFixedPoint (lift getP') numberedExpr
        case res of
            -- in the end this is what is returned
            VBase (NFALang wh) -> return . fst . unWithId $ wh
            other -> error $ "Finished eval with non-NFA result: "
                                ++ show other

    getCountAndSizes (MemoState count nfas net2nfa binMap fpcount) =
        (count, (M.size net2nfa, fst nfas, HM.size binMap), fpcount)

    initCounters = Counters (StrictTriple 0 0 0) (StrictQuad 0 0 0 0)

    bumpLeafCounter f = counters . leafC . f %= (+ 1)

    knownNet = bumpLeafCounter st1
    knownNFA = bumpLeafCounter st2
    unknownNFA = bumpLeafCounter st3

    bumpOpCounter f = counters . binOpC . f %= succ
    knownCompose = bumpOpCounter sq1
    unknownCompose = bumpOpCounter sq2
    knownTensor = bumpOpCounter sq3
    unknownTensor = bumpOpCounter sq4
    -- what to do when a fixed-point is reached at nth step
    onFixedPoint n = do
        -- fpcounter .= trace ("Setting fixed point to: " ++ show n) (Just n)
        fpcounter .= Just n

    onNet :: InterleavingMarkedNet -> NFAEvalM NFALang
    onNet (shouldInterleave, markedNet) = do
        -- If we've already seen this net we don't need to convert it again.
        mbNFA <- M.lookup markedNet <$> use net2NFA
        case mbNFA of
            Just nfa -> knownNet >> return nfa
            Nothing -> do
                let nfa = uncurry (toNFAWithMarking shouldInterleave) markedNet
                nfa' <- getOrInsert knownNFA unknownNFA
                                    (use knownNFAs) (knownNFAs %=) nfa
                net2NFA %= M.insert markedNet nfa'
                return nfa'

    onSeq :: NFALang -> NFALang -> NFAEvalM (Value NFAEvalM NFALang)
    -- Compose is an enumeration for the type of composition
    onSeq l r = doRecurse Compose l r $ \x y ->
        let badCompose =
                error $ "Couldn't compose: " ++ show x ++ " and " ++ show y
        in fromMaybe badCompose $ x `NFA.compose` y

    onTens l r = doRecurse Tensor l r NFA.tensor

    doRecurse :: OpType -> NFALang -> NFALang
              -> (NFAWithBounds -> NFAWithBounds -> NFAWithBounds)
              -> NFAEvalM (Value NFAEvalM NFALang)
    doRecurse op nfa1 nfa2 doCompose = do
        let (known, unknown) = case op of
                                   Tensor -> (knownTensor, unknownTensor)
                                   Compose -> (knownCompose, unknownCompose)
        let opTriple = (nfa1, nfa2, op)
        mbRes <- HM.lookup opTriple <$> use binOpMap
        case mbRes of
            -- if we already have that composition then we just return the value from the map
            Just nfa -> known >> return (VBase nfa)
            Nothing -> do
                unknown
                let getNFA = getOrInsert knownNFA unknownNFA (use knownNFAs)
                                         (knownNFAs %=)
                -- Reduce the resulting NFA, it can potentially be used many
                -- times.
                nfa <- getNFA . reduceNFA $
                    doCompose (toRawNFA nfa1) (toRawNFA nfa2)
                -- Insert the opTriple into the map
                binOpMap %= (HM.insert opTriple nfa)
                return $ VBase nfa

    -- See if we know a language equivalent NFA (which is reduced already),
    -- returning it if we do; reducing and remembering this NFA if we don't.
    getOrInsert :: (Functor m, Monad m) => m () -> m ()
                -> m (Int, [NFALang])
                -> (((Int, [NFALang]) -> (Int, [NFALang])) -> m ())
                -> NFAWithBounds -> m NFALang
    getOrInsert onKnown onUnknown getFrom update nfa = do
        mbExisting <-
            listToMaybe . filter (langEquiv nfa . toRawNFA) . snd <$> getFrom
        case mbExisting of
            Just found -> onKnown >> return found
            Nothing -> do
                onUnknown
                count <- fst <$> getFrom
                let nfa' = NFALang $ WithId (reduceNFA nfa) count
                update ((+ 1) *** (nfa' :))
                return nfa'

    reduceNFA :: NFAWithBounds -> NFAWithBounds
    reduceNFA =
        reflexivelyCloseNFA . modifyNFAWB (minimise 8 . epsilonCloseNFA)
    
    langEquiv :: NFAWithBounds -> NFAWithBounds -> Bool
    langEquiv (NFAWithBoundaries nfa1 l1 r1) 
              (NFAWithBoundaries nfa2 l2 r2) = l1 == l2 && r1 == r2 &&
                            equivalenceHKC nfa1 nfa2

-- this is the function that is the entry point for this module
-- acts as the outputter variable in Run.hs
expr2NFA :: IO Int -> Expr NFAWithBounds
         -> IO (NFAWithBounds, (Counters, Sizes))
expr2NFA getP expr = do
    -- Tag all the imported NFAs with their IDs
    let (numberedExpr, nfas) =
            runState (traverse initialNumbering expr) (0, [])
        initState = MemoState initCounters nfas M.empty HM.empty Nothing
    second getCountAndSizes <$> runStateT (doEval numberedExpr) initState
  where
    initialNumbering = getOrInsert (return ()) (return ()) get modify

    doEval numberedExpr = do
        res <- exprEval onNet onSeq onTens onFixedPoint (lift getP) numberedExpr
        case res of
            -- in the end this is what is returned
            VBase (NFALang wh) -> return . fst . unWithId $ wh
            other -> error $ "Finished eval with non-NFA result: "
                                ++ show other

    getCountAndSizes (MemoState count nfas net2nfa binMap _) =
        (count, (M.size net2nfa, fst nfas, HM.size binMap))

    initCounters = Counters (StrictTriple 0 0 0) (StrictQuad 0 0 0 0)

    bumpLeafCounter f = counters . leafC . f %= (+ 1)

    knownNet = bumpLeafCounter st1
    knownNFA = bumpLeafCounter st2
    unknownNFA = bumpLeafCounter st3

    bumpOpCounter f = counters . binOpC . f %= succ
    knownCompose = bumpOpCounter sq1
    unknownCompose = bumpOpCounter sq2
    knownTensor = bumpOpCounter sq3
    unknownTensor = bumpOpCounter sq4
    onFixedPoint n = do
        fpcounter .= trace ("Setting fixed point to: " ++ show n) (Just n)
    -- onParam n = fpcounter .= Just n

    onNet :: InterleavingMarkedNet -> NFAEvalM NFALang
    onNet (shouldInterleave, markedNet) = do
        -- If we've already seen this net we don't need to convert it again.
        mbNFA <- M.lookup markedNet <$> use net2NFA
        case mbNFA of
            Just nfa -> knownNet >> return nfa
            Nothing -> do
                let nfa = uncurry (toNFAWithMarking shouldInterleave) markedNet
                nfa' <- getOrInsert knownNFA unknownNFA
                                    (use knownNFAs) (knownNFAs %=) nfa
                net2NFA %= M.insert markedNet nfa'
                return nfa'

    onSeq :: NFALang -> NFALang -> NFAEvalM (Value NFAEvalM NFALang)
    -- Compose is an enumeration for the type of composition
    onSeq l r = doRecurse Compose l r $ \x y ->
        let badCompose =
                error $ "Couldn't compose: " ++ show x ++ " and " ++ show y
        in fromMaybe badCompose $ x `NFA.compose` y

    onTens l r = doRecurse Tensor l r NFA.tensor

    doRecurse :: OpType -> NFALang -> NFALang
              -> (NFAWithBounds -> NFAWithBounds -> NFAWithBounds)
              -> NFAEvalM (Value NFAEvalM NFALang)
    doRecurse op nfa1 nfa2 doCompose = do
        let (known, unknown) = case op of
                                   Tensor -> (knownTensor, unknownTensor)
                                   Compose -> (knownCompose, unknownCompose)
        let opTriple = (nfa1, nfa2, op)
        mbRes <- HM.lookup opTriple <$> use binOpMap
        case mbRes of
            -- if we already have that composition then we just return the value from the map
            Just nfa -> do
                known >> return (VBase nfa)
            Nothing -> do
                unknown
                let getNFA = getOrInsert knownNFA unknownNFA (use knownNFAs)
                                         (knownNFAs %=)
                -- Reduce the resulting NFA, it can potentially be used many
                -- times.
                nfa <- getNFA . reduceNFA $
                    doCompose (toRawNFA nfa1) (toRawNFA nfa2)
                -- Insert the opTriple into the map
                binOpMap %= (HM.insert opTriple nfa)
                return $ VBase nfa


    -- See if we know a language equivalent NFA (which is reduced already),
    -- returning it if we do; reducing and remembering this NFA if we don't.
    getOrInsert :: (Functor m, Monad m) => m () -> m ()
                -> m (Int, [NFALang])
                -> (((Int, [NFALang]) -> (Int, [NFALang])) -> m ())
                -> NFAWithBounds -> m NFALang
    getOrInsert onKnown onUnknown getFrom update nfa = do
        mbExisting <-
            listToMaybe . filter (langEquiv nfa . toRawNFA) . snd <$> getFrom
        case mbExisting of
            Just found -> onKnown >> return found
            Nothing -> do
                onUnknown
                count <- fst <$> getFrom
                let nfa' = NFALang $ WithId (reduceNFA nfa) count
                update ((+ 1) *** (nfa' :))
                return nfa'

    reduceNFA :: NFAWithBounds -> NFAWithBounds
    reduceNFA =
        reflexivelyCloseNFA . modifyNFAWB (minimise 8 . epsilonCloseNFA)
    
    langEquiv :: NFAWithBounds -> NFAWithBounds -> Bool
    langEquiv (NFAWithBoundaries nfa1 l1 r1) 
              (NFAWithBoundaries nfa2 l2 r2) = l1 == l2 && r1 == r2 &&
                            equivalenceHKC nfa1 nfa2


expr2NWB :: IO Int -> Expr MarkedNet -> IO MarkedNet
expr2NWB getP expr = do
    res <- exprEval onNet onSeq onTens onFixedPoint getP expr
    case res of
        VBase b -> return b
        other -> error $ "Finished eval with non-nwb result: " ++ show other
  where
    onNet = return . snd
    onSeq mn1 mn2 =
        let badCompose =
                error $ "Couldn't compose: " ++ show mn1 ++ " and " ++ show mn2
            mn = fromMaybe badCompose $ mn1 `Nets.composeMarkedNet` mn2
        in return $ VBase mn
    onTens (m1, n1) (m2, n2) =
        return $ VBase (concatMarkingList m1 m2, Nets.tensor n1 n2)

    onFixedPoint _ = do
        return ()


data SlowCounters = SlowCounters
    { _sleafC :: !Int               -- # of leaves converted
    , _sCompC :: !Int               -- # of sequential compositions performed
    , _sTensC :: !Int               -- # of tensor compositions performed
    , _sMaxNFAStateSize :: !MaxComp -- Biggest NFA size (# states) seen
    }

$(makeLenses ''SlowCounters)

instance NFData SlowCounters where
    rnf (SlowCounters l s t m) =
        rnf l `seq` rnf s `seq` rnf t `seq` rnf m `seq` ()

instance Show SlowCounters where
    show (SlowCounters leaves seqs tens maxS) = show (leaves, seqs, tens, maxS)

type NFASlowEvalM = StateT SlowCounters IO

-- Do not perform any memoisation or minimisation optimisation steps. A hacky,
-- copy-paste from expr2NFA, but we don't seriously expect to use this!
expr2NFASlow :: IO Int -> Expr NFAWithBounds
             -> IO (NFAWithBounds, SlowCounters)
expr2NFASlow getP expr = do
    let initState = SlowCounters 0 0 0 $ MaxComp (0, (0, 0))
    flip runStateT initState $ do
        res <- exprEval onNet onSeq onTens onFixedPoint (lift getP) expr
        case res of
            VBase wh -> return wh
            other -> error $ "Finished eval with non-NFA result: "
                                ++ show other
  where
    bumper f = f %= succ

    bumpLeafCounter = bumper sleafC
    bumpSeqCounter = bumper sCompC
    bumpTensCounter = bumper sTensC

    onNet (shouldInterleave, markedNet) = do
        let nfa = uncurry (toNFAWithMarking shouldInterleave) markedNet
        bumpLeafCounter
        return nfa

    nfaStates :: NFAWithBounds -> Integer
    nfaStates (NFAWithBoundaries (NFA lts _ _) _ _) =
        fromIntegral . S.size $ statesLTS lts

    onSeq l r = doRecurse Compose l r $ \x y ->
        let badCompose =
                error $ "Couldn't compose: " ++ show x ++ " and " ++ show y
        in fromMaybe badCompose $ x `NFA.compose` y

    onTens l r = doRecurse Tensor l r NFA.tensor

    doRecurse :: OpType -> NFAWithBounds -> NFAWithBounds
              -> (NFAWithBounds -> NFAWithBounds -> NFAWithBounds)
              -> NFASlowEvalM (Value NFASlowEvalM NFAWithBounds)
    doRecurse op nfa1 nfa2 doCompose = do
        let bump = case op of
                          Compose -> bumpSeqCounter
                          Tensor -> bumpTensCounter
        bump
        maxComp <- use sMaxNFAStateSize
        let nfa1Size = nfaStates nfa1
            nfa2Size = nfaStates nfa2
            maxComp' = MaxComp (nfa1Size * nfa2Size, (nfa1Size, nfa2Size))
        when (maxComp <= maxComp') $
            sMaxNFAStateSize .= maxComp'
        return . VBase $ doCompose nfa1 nfa2

    onFixedPoint _ = do
        return ()


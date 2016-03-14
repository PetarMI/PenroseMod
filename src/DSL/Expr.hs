{-# LANGUAGE ScopedTypeVariables, TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module DSL.Expr
    ( RawExpr(..)
    , Type(..)
    , Expr(..)
    , SugarExpr(..)
    , BinOp(..)
    , Value(..)
    , VarId(..)
    , InterleavingMarkedNet
    , checkType
    , TypeCheckError(..)
    , exprSkeleton
    , reassocExpr
    ) where

import Control.Applicative ( (<$>), (<*>) )
import Control.Monad ( when )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT, Reader, runReader )
import Control.Monad.Reader ( local, ask )
import Data.Foldable ( Foldable )
import Data.Traversable ( Traversable )
import Safe ( atMay )
import Util ( ReassocResult(..), ReassocType(..), (<||>) )
import Debug.Trace

import Nets ( NetWithBoundaries(..), MarkedNet )

-- Should the net be converted to an NFA using interleaving semantics?
type InterleavingMarkedNet = (Bool, MarkedNet)

data BinOp = Add
           | Sub
           deriving (Eq, Show)

newtype VarId = VarId { varToInt :: Int }
              deriving (Eq, Ord, Show)

-- 'SugarExpr p' contains precomputed values of type @p@, and includes a
-- SENSequence term which is desugared by the typechecker into a fold.
data SugarExpr p = SEVar VarId
                 | SENum Int
                 | SERead
                 | SEIntCase (SugarExpr p) (SugarExpr p) (SugarExpr p)
                 | SEStarCase (SugarExpr p) (SugarExpr p) (SugarExpr p)
                 | SENSequence (SugarExpr p) (SugarExpr p)
                 | SEkstar (SugarExpr p)
                 | SEBin BinOp (SugarExpr p) (SugarExpr p)
                 | SEConstant InterleavingMarkedNet
                 | SEPreComputed p
                 | SEApp (SugarExpr p) (SugarExpr p)
                 | SELam Type (SugarExpr p)
                 | SEBind (SugarExpr p) (SugarExpr p)
                 | SESeq (SugarExpr p) (SugarExpr p)
                 | SETen (SugarExpr p) (SugarExpr p)
                 deriving (Eq, Show)

-- 'Expr p' contains precomputed values of type @p@.
data Expr p = EVar VarId
            | ENum Int
            | ERead
            | EIntCase (Expr p) (Expr p) (Expr p)
            | EStarCase (Expr p) (Expr p) (Expr p) (Expr p)
            | EBin BinOp (Expr p) (Expr p)
            | EConstant InterleavingMarkedNet
            | EPreComputed p
            | EApp (Expr p) (Expr p)
            | ELam (Expr p)
            | EBind (Expr p) (Expr p)
            | ESeq (Expr p) (Expr p)
            | ETen (Expr p) (Expr p)
            deriving (Eq, Show, Functor, Foldable, Traversable)

data Type = TyInt
          | TyArr Int Int
          | Type :-> Type
          deriving (Eq, Ord, Show)
infixr :->


-- Before resolving names, we can't tell between imports/constants.
data RawExpr = RVar VarId
             | RNum Int
             | RRead
             | RIntCase RawExpr RawExpr RawExpr
             | RStarCase RawExpr RawExpr RawExpr
             | RNSequence RawExpr RawExpr
             | RKStar RawExpr
             | RBin BinOp RawExpr RawExpr
             | RName String
             | RApp RawExpr RawExpr
             | RLam Type RawExpr
             | RBind RawExpr RawExpr
             | RSeq RawExpr RawExpr
             | RTen RawExpr RawExpr
             deriving (Eq, Show)

-- Use a HOAS representation to avoid substitution/name-capture.
-- represents the output of exprEval
-- a value can finish as a lambda but nothing to apply it to
-- a base type with a value p that depending on the mode can be net or an NFA
data Value m p = VLam (Value m p -> m (Value m p))
               | VBase p
               | VInt Int

instance (Show p) => Show (Value m p) where
    show (VLam _) = "VLam <thunk>"
    show (VBase b) = "VBase " ++ show b
    show (VInt i) = "VInt " ++ show i

instance (Eq p) => Eq (Value m p) where
    (VBase b1) == (VBase b2) = b1 == b2
    (VInt i) == (VInt n) = i == n
    _ == _ = False

data TypeConstraint = TCEquality Type Type

data TypeCheckError = IncompatableTypes Type Type
                    | VariableOutOfRange Int
                    | InvalidCompose Int Int Int Int
                    | NotInt Type
                    | InvalidSeqType Type
                    | NotArrType Type
                    | NotAFunction Type
                    deriving ( Eq, Ord, Show )

newtype Context = Ctx [Type] deriving Show

emptyContext :: Context
emptyContext = Ctx []

getNthTypeFromContext :: Int -> Context -> Maybe Type
getNthTypeFromContext i (Ctx ctx) = ctx `atMay` i

addTypeBindingToContext :: Type -> Context -> Context
addTypeBindingToContext ts (Ctx c) = Ctx $ ts : c

type TypeCheckM a = ReaderT Context (Either TypeCheckError) a
type GetBounds t = t -> (Int, Int)

-- 'checkType' is parameterised by a function to get the bounds of a
-- pre-computed result, to ensure well-typed compositions. We generate a
-- de-sugared term that doesn't contain type annotations on lambdas or
-- NSequence terms (they are turned into suitable intcases)
checkType :: forall t . Show t => GetBounds t -> SugarExpr t
          -> Either TypeCheckError (Expr t, Type)
checkType getBounds term = runReaderT (checkType' term) emptyContext
  where
    die = lift . Left

    checkInt e = do
        (e', eTy) <- checkType' e
        when (eTy /= TyInt) $ die $ NotInt eTy
        return e'

    -- We use a Reader containing the context,
    checkType' :: SugarExpr t -> TypeCheckM (Expr t, Type)
    checkType' subTerm = case subTerm of
        SERead -> return (ERead, TyInt)
        (SENum n) -> return (ENum n, TyInt)
        (SEBin o x y) -> do
            x' <- checkInt x
            y' <- checkInt y
            return (EBin o x' y', TyInt)
        (SEVar vid) -> do
            ctx <- ask
            let offset = varToInt vid
            case getNthTypeFromContext offset ctx of
                Nothing -> die $ VariableOutOfRange offset
                Just t -> return (EVar vid, t)
        n@(SEConstant c) -> (EConstant c,) <$> getNetType n
        (SEPreComputed p) -> case getBounds p of
            (l, r) -> return (EPreComputed p, TyArr l r)
        (SEApp fun arg) -> do
            (fun', funTy) <- checkType' fun
            (arg', argTy) <- checkType' arg
            case funTy of
                (funArgTy :-> resType) -> do
                    checkTypeConstraint $ TCEquality funArgTy argTy
                    return (EApp fun' arg', resType)
                _ -> die $ NotAFunction funTy
        (SEIntCase i zeroCase succCase) -> do
            (i', iTy) <- checkType' i
            when (iTy /= TyInt) $ die $ NotInt iTy
            (zeroCase', zTy) <- checkType' zeroCase
            (succCase', sTy) <- checkType' succCase
            checkTypeConstraint $ TCEquality sTy (zTy :-> zTy)
            return (EIntCase i' zeroCase' succCase', zTy)
        (SEStarCase i zeroCase succCase) -> do
            (i', iTy) <- checkType' i
            when (iTy /= TyInt) $ die $ NotInt iTy
            (zeroCase', zTy) <- checkType' zeroCase
            (succCase', sTy) <- checkType' succCase
            checkTypeConstraint $ TCEquality sTy (zTy :-> zTy)
            return (EStarCase i' zeroCase' succCase' (ENum 1), zTy)
        (SENSequence num net) -> do
            (_, netTy) <- checkType' net
            let varExpr = SEVar . VarId
                -- We are placing the net inside a bind, so we must offset
                -- any free vars in expr net to take account of the bound variable
                -- We use a pair of binds so that the num/net expressions are only evaluated once
                -- when evaluating the IntCase.
                dsExpr = SEBind num $
                               SEBind (offsetVarsBy 1 net) $
                                     SEIntCase (SEBin Sub (varExpr 1) (SENum 1))
                                               (varExpr 0)
                                               (SELam netTy (SESeq (varExpr 0)
                                                                   (varExpr 1)))
            case netTy of
                TyArr x y
                    | x == y -> do
                    -- Sanity check
                    -- (dsExpr', dsExprType) <- trace (show dsExpr) (checkType' dsExpr) 
                    (dsExpr', dsExprType) <- checkType' dsExpr
                    if dsExprType /= netTy
                        then error $ "dsExprType is not netTy: "
                                     ++ show dsExprType ++ " /= "
                                     ++ show netTy
                        else return (dsExpr', netTy)
                _ -> die $ InvalidSeqType netTy
        (SEkstar net) -> do
            (_, netTy) <- checkType' net
            let varExpr = SEVar . VarId
                -- TODO
                -- out of curiousity try binding the num to SERead as well
                -- shouldnt make any difference 
                dsExpr = SEBind net $
                               SEStarCase (SEBin Sub SERead (SENum 1))
                                          (varExpr 0)
                                          (SELam netTy (SESeq (varExpr 0)
                                                              (varExpr 1)))

            case netTy of
                TyArr x y 
                    | x == y -> do
                        -- desugaring of SEkstar to EStarCase
                        -- (dsExpr', dsExprType) <- trace (show dsExpr) (checkType' dsExpr) 
                        (dsExpr', dsExprType) <- offsetStarCase <$> checkType' dsExpr
                        if dsExprType /= netTy
                            then error $ "dsExprType is not netTy: "
                                         ++ show dsExprType ++ " /= "
                                         ++ show netTy
                            else return (dsExpr', netTy)
                _ -> die $ InvalidSeqType netTy
        (SELam argTy body) -> do
            (body', bodyTy) <- local (addTypeBindingToContext argTy) $ checkType' body
            return (ELam body', argTy :-> bodyTy)
        (SEBind expr body) -> do
            (expr', exprType) <- checkType' expr
            (body', bodType) <- local (addTypeBindingToContext exprType) $
                checkType' body
            return (EBind expr' body', bodType)
        (SESeq e1 e2) -> checkSeq e1 e2
        (SETen e1 e2) -> checkTensor e1 e2

    -- Ugh, ugly!
    -- We use a Reader context to track the number of binders encountered, any variables that are
    -- greater than this number are incremented (since they are free).
    offsetVarsBy n se = runReader (go se) 0
      where
        go :: SugarExpr t -> Reader Int (SugarExpr t)
        go (SEVar (VarId x)) = do
            binderCount <- ask
            let varOffset = if x < binderCount then 0 else n
            return $ SEVar (VarId $ x + varOffset)
        go (SEIntCase se1 se2 se3) = SEIntCase <$> go se1 <*> go se2 <*> go se3
        go (SENSequence se1 se2) = SENSequence <$> go se1 <*> go se2
        go (SEBin b se1 se2) = SEBin b <$> go se1 <*> go se2
        go (SEApp se1 se2) = SEApp <$> go se1 <*> go se2
        go (SELam t se1) = do
            offsetBody <- local (+ 1) (go se1)
            return $ SELam t offsetBody
        go (SEBind se1 se2) = do
            offsetBoundExpr <- go se1
            -- We do not have recursive bindings - only the body is offset with an increased binder
            -- count
            offsetBody <- local (+ 1) (go se2)
            return $ SEBind offsetBoundExpr offsetBody
        go (SESeq se1 se2) = SESeq <$> go se1 <*> go se2
        go (SETen se1 se2) = SETen <$> go se1 <*> go se2
        go x = return x

    -- offsetStarCase :: Expr p -> Expr p
    offsetStarCase (EBind v (EStarCase i z s _), t) = (EBind v (EStarCase i z s (ENum 0)), t)
    offsetStarCase n                        = trace (show n) (error "Offsetting Error when desugaring")
 
    getNetType net = return $ case net of
            (SEConstant (_, (_, NetWithBoundaries l r _ _ _ _))) -> TyArr l r
            _ -> error "getNetType on non-net!"

    checkNetOp e1 e2 = do
        (e1', e1Ty) <- checkType' e1
        (e2', e2Ty) <- checkType' e2
        case (e1Ty, e2Ty) of
            (TyArr _ _, TyArr _ _) -> return (e1', e2', e1Ty, e2Ty)
            (TyArr _ _, y) -> die $ NotArrType y
            (x, TyArr _ _) -> die $ NotArrType x
            -- Pick x, because our messages are crappy anyway.
            (x, _) -> die $ NotArrType x

    checkTensor e1 e2 = do
        (e1', e2', TyArr x y, TyArr w z) <- checkNetOp e1 e2
        return (ETen e1' e2', TyArr (x + w) (y + z))

    checkSeq e1 e2 = do
        (e1', e2', TyArr x y, TyArr w z) <- checkNetOp e1 e2
        if y == w
            then return (ESeq e1' e2', TyArr x z)
            else die $ InvalidCompose x y w z

    checkTypeConstraint ::  TypeConstraint -> TypeCheckM ()
    checkTypeConstraint (TCEquality ty1 ty2) = case (ty1, ty2) of
        (TyInt, TyInt) -> return ()
        (TyArr x y, TyArr z w)
            | x == z && y == w -> return ()
        (t1 :-> t2, t3 :-> t4) -> do
            checkTypeConstraint $ TCEquality t1 t3
            checkTypeConstraint $ TCEquality t2 t4
        _ -> die $ IncompatableTypes ty1 ty2

reassocExpr :: Expr t -> (Expr t, ReassocResult)
reassocExpr expr = takeExpr $ reassocExpr' expr ReassocFail []
  where 
    reassocExpr' :: Expr t -> ReassocResult -> [Expr t] -> (Expr t, ReassocResult, [Expr t])
    reassocExpr' expr' reassoc boundExprs = case expr' of
        (ENum n) -> (ENum n, reassoc, boundExprs)
        ERead    -> (ERead, reassoc, boundExprs)
        (EBin op x y) -> (EBin op x y, reassoc, boundExprs)
        (EIntCase n term f) -> (EIntCase n term f, reassoc, boundExprs)
        (EStarCase n term f offset) -> (EStarCase n term f offset, reassoc, boundExprs)
        (EPreComputed pc) -> (EPreComputed pc, reassoc, boundExprs)
        (EConstant c) -> (EConstant c, reassoc, boundExprs)
        (ESeq t1 t2) -> 
            let (nexpr, reassoc1, boundExprs') = reassocSequence (ESeq t1 t2) boundExprs
            in (nexpr, reassoc <||> reassoc1, boundExprs')
        (ETen t1 t2) -> 
            let (et1, reassoc1, boundExprs1) = reassocExpr' t1 reassoc boundExprs
                (et2, reassoc2, boundExprs2) = reassocExpr' t2 reassoc boundExprs
            in (ETen et1 et2, reassoc <||> reassoc1 <||> reassoc2, boundExprs)
        (EVar v) -> (EVar v, reassoc, boundExprs)
        (EApp f param) ->  
            let (f', reassoc1, boundExprs1) = reassocExpr' f reassoc boundExprs
                (param', reassoc2, boundExprs2) = reassocExpr' param reassoc boundExprs
            in (EApp f' param', reassoc <||> reassoc1 <||> reassoc2, boundExprs)
        (ELam body) -> 
            let (body', reassoc1, boundExprs') = reassocExpr' body reassoc boundExprs
            in (ELam body', reassoc <||> reassoc1, boundExprs')
        (EBind e1 body) -> 
            let (e1', reassoc1, boundExprs1) = reassocExpr' e1 reassoc boundExprs
                (body', reassoc2, boundExprs2) = reassocExpr' body reassoc (e1 : boundExprs)
            in (EBind (head boundExprs2) body', reassoc <||> reassoc1 <||> reassoc2, (tail boundExprs2))

    reassocSequence :: Expr t -> [Expr t] -> (Expr t, ReassocResult, [Expr t])
    reassocSequence expr' boundExprs = case expr' of 
        (ESeq e (EStarCase n term (ELam (ESeq t1 t2)) offset)) -> 
                ((ESeq (EStarCase n e (ELam (ESeq t2 t1)) offset) term), (ReassocApplied LeftAssoc), boundExprs) 
        (ESeq (EStarCase n term (ELam (ESeq t1 t2)) offset) e) -> 
                ((ESeq term (EStarCase n e (ELam (ESeq t2 t1)) offset)), (ReassocApplied RightAssoc), boundExprs)
        (ESeq const' (EVar v)) -> 
            let (intCase, term, reassocRes) = reassocIntCase (EVar v) const' RightAssoc boundExprs
                boundExprs' = substitudeIntCase intCase (varToInt v) boundExprs
            in case reassocRes of 
                (ReassocApplied a) -> ((ESeq (EVar v) term), reassocRes, boundExprs')
                ReassocFail -> ((ESeq const' (EVar v)), reassocRes, boundExprs)
        (ESeq (EVar v) const') -> 
            let (intCase, term, reassocRes) = reassocIntCase (EVar v) const' LeftAssoc boundExprs
                boundExprs' = substitudeIntCase intCase (varToInt v) boundExprs
            in case reassocRes of 
                (ReassocApplied a) -> ((ESeq term (EVar v)), reassocRes, boundExprs')
                ReassocFail -> ((ESeq (EVar v) const'), reassocRes, boundExprs)
        _ -> (expr', ReassocFail, boundExprs)

    -- 1st arg - the variable that we resolve
    -- 2nd arg - constant that will go in the lambda
    -- 3rd arg - type of association that the expression has before reassociating
    -- 4th arg - environment with bindings 
    -- return
    --    the intcase which we have to rebind
    --    the term from the lambda that becomes an arg in the sequence composition 
    --    has association been applied
    reassocIntCase :: Expr t -> Expr t -> ReassocType -> [Expr t] -> (Expr t, Expr t, ReassocResult)
    reassocIntCase (EVar v) const' assocType boundExprs = 
        let varExpr = boundExprs !! varToInt v
        in case (varExpr, assocType) of
            ((EStarCase n term (ELam (ESeq t (EVar v'))) offset), RightAssoc) -> 
                ((EStarCase n const' (ELam (ESeq (EVar v') t)) offset), term, (ReassocApplied LeftAssoc))
            ((EStarCase n term (ELam (ESeq (EVar v') t)) offset), LeftAssoc) ->
                ((EStarCase n const' (ELam (ESeq t (EVar v'))) offset), term, (ReassocApplied RightAssoc))
            _ -> ((EVar v), const', ReassocFail)
    reassocIntCase _ _ _ _ = error "Error while reassociating IntCase"

    substitudeIntCase :: Expr t -> Int -> [Expr t] -> [Expr t]
    substitudeIntCase intCase 0 (x:xs) = (intCase : xs)
    substitudeIntCase intCase n (x:xs) = x : (substitudeIntCase intCase (n - 1) xs)
    substitudeIntCase _ _ []           = error "Error while reassociating variable binding"

    takeExpr res = case res of 
        (expr', reassocRes, _) -> (expr', reassocRes)

exprSkeleton :: forall t . Show t => Expr t -> String
exprSkeleton expr = exprSkeleton' expr 0 2
  where
    exprSkeleton' :: Expr t -> Int -> Int -> String
    exprSkeleton' expr' offset n = case expr' of
        (EBind e body) -> 
            let top = addOffset "Bind" offset
                ch1 = exprSkeleton' e (offset + n) n
                ch2 = exprSkeleton' body (offset + n) n
            in  top ++ ch1 ++ ch2
        (ELam body) -> 
            let top = addOffset "Lambda" offset
                ch  = exprSkeleton' body (offset + n) n
            in top ++ ch
        (ESeq e1 e2) -> 
            let top = addOffset "Sequence composition" offset
                ch1 = exprSkeleton' e1 (offset + n) n
                ch2 = exprSkeleton' e2 (offset + n) n
            in top ++ ch1 ++ ch2
        (ETen e1 e2) -> 
            let top = addOffset "Tensor product" offset
                ch1 = exprSkeleton' e1 (offset + n) n
                ch2 = exprSkeleton' e2 (offset + n) n
            in top ++ ch1 ++ ch2
        (EIntCase _ term f) -> 
            let top = addOffset "IntCase" offset
                ch1 = exprSkeleton' term (offset + n) n
                ch2 = exprSkeleton' f (offset + n) n
            in top ++ ch1 ++ ch2
        (EStarCase _ term f (ENum i)) -> 
            let op  = if i == 1 then "StarCase" else "N_Sequence" 
                top = addOffset op offset
                ch1 = exprSkeleton' term (offset + n) n
                ch2 = exprSkeleton' f (offset + n) n
            in top ++ ch1 ++ ch2
        (EPreComputed _) ->
            let top = addOffset "Precomputed" offset
            in top
        (EConstant _) ->
            let top = addOffset "Constant" offset
            in top
        (EVar _) ->
            let top = addOffset "Variable" offset
            in top
        (EApp _ _) -> 
            let top = addOffset "Application" offset
            in top
        _ -> addOffset "Blargh" offset 

addOffset :: String -> Int -> String
addOffset str 0 = str ++ "\n"
addOffset str n = ' ' : (addOffset str (n - 1))

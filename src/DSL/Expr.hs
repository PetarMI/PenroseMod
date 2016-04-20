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
-- SENSequence and SEkstar terms are desugared by the typechecker into a fold.
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

-- used for fixed-point detection
-- if p is NFA with boundaries it checks internally for weak language equivalence
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
        -- typecheck the starcase 
        -- hidden parameters indicates this is originally a starcase op
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
                -- desugar ** into a starcase
                -- build new expression and ensure free variables are offset 
                dsExpr = SEBind net $
                               SEStarCase (SEBin Sub SERead (SENum 1))
                                          (varExpr 0)
                                          (SELam netTy (SESeq (varExpr 0)
                                                              (varExpr 1)))

            case netTy of
                TyArr x y 
                    | x == y -> do
                        -- typecheck the new expression
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
    -- used to say the starcase is actually **
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

-- main Reassociating function 
reassocExpr :: (Show t) => Expr t -> (Expr t, ReassocResult)
reassocExpr expr = takeExpr $ reassocExpr' expr ReassocFail []
  where 
    -- look for sequential compositions of the supported form and try to reassociate them
    reassocExpr' :: (Show t) => Expr t -> ReassocResult -> [Expr t] -> (Expr t, ReassocResult, [Expr t])
    reassocExpr' expr' reassoc env = case expr' of
        (ENum n) -> (ENum n, reassoc, env)
        ERead    -> (ERead, reassoc, env)
        (EBin op x y) -> (EBin op x y, reassoc, env)
        (EIntCase n term f) -> (EIntCase n term f, reassoc, env)
        (EStarCase n term f offset) -> (EStarCase n term f offset, reassoc, env)
        (EPreComputed pc) -> (EPreComputed pc, reassoc, env)
        (EConstant c) -> (EConstant c, reassoc, env)
        (ESeq t1 t2) -> 
            let (nexpr, reassoc1, env') = reassocSequence (ESeq t1 t2) env
            in (nexpr, reassoc <||> reassoc1, env')
        (ETen t1 t2) -> 
            let (et1, reassoc1, _) = reassocExpr' t1 reassoc env
                (et2, reassoc2, _) = reassocExpr' t2 reassoc env
            in (ETen et1 et2, reassoc <||> reassoc1 <||> reassoc2, env)
        (EVar v) -> (EVar v, reassoc, env)
        (EApp f param) ->  
            let (f', reassoc1, _) = reassocExpr' f reassoc env
                (param', reassoc2, _) = reassocExpr' param reassoc env
            in (EApp f' param', reassoc <||> reassoc1 <||> reassoc2, env)
        (ELam body) -> 
            let (body', reassoc1, env') = reassocExpr' body reassoc env
            in (ELam body', reassoc <||> reassoc1, env')
        (EBind e1 body) -> 
            let (_, reassoc1, _) = reassocExpr' e1 reassoc env
                (body', reassoc2, env2) = reassocExpr' body reassoc (e1 : env)
            in (EBind (head env2) body', reassoc <||> reassoc1 <||> reassoc2, (tail env2))

    -- when a sequential composition is found check if it forms a left or right deep tree using a starcase
    reassocSequence :: (Show t) => Expr t -> [Expr t] -> (Expr t, ReassocResult, [Expr t])
    reassocSequence expr' env = case expr' of 
        (ESeq e (EStarCase n term (ELam (ESeq t1 (EVar v))) offset)) -> 
                ((ESeq (EStarCase n e (ELam (ESeq (EVar v) t1)) offset) term), (ReassocApplied LeftAssoc), env) 
        (ESeq (EStarCase n term (ELam (ESeq (EVar v) t2)) offset) e) -> 
                ((ESeq term (EStarCase n e (ELam (ESeq t2 (EVar v))) offset)), (ReassocApplied RightAssoc), env)
        -- handle the case where they are both variables
        (ESeq (EVar v1) (EVar v2)) ->
            let (EVar fold, EVar v, assoc) = findAssociation (EVar v1) (EVar v2) env
                (intCase, term, reassocRes) = reassocIntCase (EVar fold) (EVar v) assoc env
                env' = substitudeIntCase intCase (varToInt fold) env
            in case (reassocRes, assoc) of 
                (ReassocApplied _, RightAssoc) -> ((ESeq (EVar fold) term), reassocRes, env')
                (ReassocApplied _, LeftAssoc) -> ((ESeq term (EVar fold)), reassocRes, env')
                (ReassocFail, _) -> (expr', reassocRes, env)
                _                -> (expr', reassocRes, env)  -- this is ReassocNotAttempted but it is impossible to go there
        -- handle cases where the starcase is a variable
        (ESeq operand (EVar v)) -> 
            let (intCase, term, reassocRes) = reassocIntCase (EVar v) operand RightAssoc env
                env' = substitudeIntCase intCase (varToInt v) env
            in case reassocRes of 
                (ReassocApplied _) -> ((ESeq (EVar v) term), reassocRes, env')
                ReassocFail -> (expr', reassocRes, env)
                _           -> (expr', reassocRes, env)  -- this is ReassocNotAttempted but it is impossible to go there
        (ESeq (EVar v) operand) -> 
            let (intCase, term, reassocRes) = reassocIntCase (EVar v) operand LeftAssoc env
                env' = substitudeIntCase intCase (varToInt v) env
            in case reassocRes of 
                (ReassocApplied _) -> ((ESeq term (EVar v)), reassocRes, env')
                ReassocFail -> (expr', reassocRes, env)
                _           -> (expr', reassocRes, env)  -- this is ReassocNotAttempted but it is impossible to go there
        _ -> (expr', ReassocFail, env)

    -- 1st arg - the variable that we resolve
    -- 2nd arg - constant that will go in the lambda
    -- 3rd arg - type of association that the expression has before reassociating
    -- 4th arg - environment with bindings 
    -- return
    --    the intcase which we have to rebind
    --    the term from the lambda that becomes an arg in the sequence composition 
    --    has association been applied
    reassocIntCase :: Expr t -> Expr t -> ReassocType -> [Expr t] -> (Expr t, Expr t, ReassocResult)
    reassocIntCase (EVar v) operand assocType env = 
        let varExpr = env !! varToInt v
        in case (varExpr, assocType) of
            ((EStarCase n term (ELam (ESeq t (EVar v'))) offset), RightAssoc) -> 
                let noperand = (offsetVar term env)
                    (nterm, bindOk) = (offsetOperand operand (EVar v))
                in case bindOk of 
                    True -> ((EStarCase n nterm (ELam (ESeq (EVar v') t)) offset), noperand, (ReassocApplied LeftAssoc))
                    False -> ((EVar v), operand, ReassocFail)
            ((EStarCase n term (ELam (ESeq (EVar v') t)) offset), LeftAssoc) ->
                let noperand = (offsetVar term env)
                    (nterm, bindOk) = (offsetOperand operand (EVar v))
                in case bindOk of 
                    True -> ((EStarCase n nterm (ELam (ESeq t (EVar v'))) offset), noperand, (ReassocApplied RightAssoc))
                    False -> ((EVar v), operand, ReassocFail)
            _ -> ((EVar v), operand, ReassocFail)
    reassocIntCase _ _ _ _ = error "Error while reassociating IntCase"

    -- update the environment with the reassociated starcase
    substitudeIntCase :: Expr t -> Int -> [Expr t] -> [Expr t]
    substitudeIntCase intCase 0 (_:xs) = (intCase : xs)
    substitudeIntCase intCase n (x:xs) = x : (substitudeIntCase intCase (n - 1) xs)
    substitudeIntCase _ _ []           = error "Error while reassociating variable binding"

    -- find where the starcase is defined 
    findAssociation :: Expr t -> Expr t -> [Expr t] -> (Expr t, Expr t, ReassocType)
    findAssociation (EVar v1) (EVar v2) env = 
        let varExpr1 = env !! varToInt v1
            varExpr2 = env !! varToInt v2
        in case (varExpr1, varExpr2) of
            (EStarCase _ _ _ _, _) -> ((EVar v1), (EVar v2), LeftAssoc)
            (_, EStarCase _ _ _ _) -> ((EVar v2), (EVar v1), RightAssoc)
            _                      -> error "Error while searching for a bound StarCase"

    -- offset a variabe which becomes a new term in the outer sequential operation
    offsetVar :: Expr t -> [Expr t] -> Expr t
    offsetVar expr' env = case expr' of 
        (EVar (VarId n)) -> 
            let foldPos = findFold env 
            in (EVar (VarId (n + foldPos + 1)))
        _                -> expr'

    -- function to offset the operand in the sequence operation
    -- and put it within the fold with pointing to the correct binding
    -- the operand thus becomes the new term in the fold
    offsetOperand :: Expr t -> Expr t -> (Expr t, Bool)
    offsetOperand (EVar operand) (EVar fold) = 
        let operandPos = varToInt operand
            foldPos    = varToInt fold
        in if operandPos > foldPos
                then (EVar . VarId $ (operandPos - foldPos - 1), True)
                else (EVar operand, False)
    offsetOperand op _ = (op, True)

    -- check if there is a starcase definded above
    -- used to decide by how much the variables should be offset
    findFold :: [Expr t] -> Int
    findFold env = findFold' env 0
        where
            findFold' :: [Expr t] -> Int -> Int
            findFold' [] _ = error "No EStarCase found"
            findFold' (op : es) n = case op of 
                (EStarCase _ _ _ _) -> n
                _                   -> findFold' es (n + 1)

    -- return only the expression after reassociating 
    takeExpr res = case res of 
        (expr', reassocRes, _) -> (expr', reassocRes)

    {-- can be used by possible extension
    substitudeVar :: Expr t -> [Expr t] -> Expr t
    substitudeVar expr env = case expr of 
        (EVar (VarId n)) -> (env !! (n + 1))
        _                -> expr
    --}

-- function that is used for pretty printing of the wiring expression
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

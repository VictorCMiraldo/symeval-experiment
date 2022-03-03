{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module SymEval.Solver where

import Control.Monad.IO.Class
import Control.Monad.Reader
import qualified Data.Map as M
import qualified SimpleSMT
import Control.Monad.State.Class
import Control.Monad.Except
import Control.Applicative
import Data.Either
import SymEval.Pretty
import Data.Void
import SymEval.Term
import Prettyprinter hiding (Pretty, pretty)
import Data.List (intersperse)

-- | SMT Constraints:
data AtomicConstraint
  = String :== Term Var
  | Eq (Term Var) (Term Var)
  deriving (Eq , Show)

data Constraint = And [AtomicConstraint] | Bottom

instance  Pretty AtomicConstraint where
  pretty (n :== term) =
    pretty n <+> "↦" <+> pretty term
  pretty (Eq t u) =
    pretty t <+> "==" <+> pretty u

instance Pretty Constraint where
  pretty (And []) =
    "⊤"
  pretty (And l) =
    mconcat $ intersperse "\n∧ " (map pretty l)
  pretty Bottom =
    "⊥"

instance Semigroup Constraint where
  (<>) = andConstr

instance Monoid Constraint where
  mempty = And []

andConstr :: Constraint -> Constraint -> Constraint
andConstr Bottom _ = Bottom
andConstr _ Bottom = Bottom
andConstr (And l) (And m) = And (l ++ m)

-- | Solver monad for a specific solver, passed as a phantom type variable @s@ (refer to 'IsSolver' for more)
--  to know the supported solvers. That's a phantom type variable used only to distinguish
--  solver-specific operations, such as initialization
newtype SolverT s m a = SolverT {unSolverT :: ReaderT SimpleSMT.Solver m a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadReader SimpleSMT.Solver, MonadIO)

instance MonadTrans (SolverT s) where
  lift = SolverT . lift

deriving instance MonadState s m => MonadState s (SolverT sol m)
deriving instance MonadError e m => MonadError e (SolverT sol m)
deriving instance Alternative m => Alternative (SolverT sol m)

-- | Runs a computation that requires a session with a solver. You can specify
--  which solver you want through a type application:
--
--  > runSolverT @CVC4 ...
runSolverT :: forall s m a. (MonadIO m, IsSolver s) => SolverT s m a -> m a
runSolverT (SolverT comp) = launchSolver @s >>= runReaderT comp

-- | Returns 'Sat', 'Unsat' or 'Unknown' for the current solver session.
checkSat :: (MonadIO m) => SolverT s m SimpleSMT.Result
checkSat = ask >>= liftIO . SimpleSMT.check

-- | Pushes the solver context, creating a checkpoint. This is useful if you plan to execute
--  many queries that share definitions. A typical use pattern would be:
--
--  > declareDatatypes ...
--  > forM_ varsAndExpr $ \(vars, expr) -> do
--  >   solverPush
--  >   declareVariables vars
--  >   assert expr
--  >   r <- checkSat
--  >   solverPop
--  >   return r
solverPush :: (MonadIO m) => SolverT s m ()
solverPush = ask >>= liftIO . SimpleSMT.push

-- | Pops the current checkpoint, check 'solverPush' for an example.
solverPop :: (MonadIO m) => SolverT s m ()
solverPop = ask >>= liftIO . SimpleSMT.pop

-- | Declare (name and type) all the variables of the environment in the SMT
-- solver. This step is required before asserting constraints mentioning any of these variables.
declareVariables :: (MonadIO m) => M.Map String Type -> ExceptT String (SolverT s m) ()
declareVariables = mapM_ (uncurry declareVariable) . M.toList

-- | Declares a single variable in the current solver session.
declareVariable :: (MonadIO m) => String -> Type -> ExceptT String (SolverT s m) ()
declareVariable varName varTy = do
  solver <- ask
  ty <- translateType varTy
  liftIO $ void $ SimpleSMT.declare solver (toSmtName varName) ty

-- | Asserts a constraint; check 'Constraint' for more information
-- | The functions 'assert' and 'assertNot' output a boolean,
-- stating if the constraint was fully passed to the SMT solver,
-- or if a part was lost during the translation process.
assert ::
  (MonadIO m) =>
  Constraint ->
  SolverT s m Bool
assert c =
  SolverT $ ReaderT $ \solver -> do
    (isTotal,expr) <- constraintToSExpr c
    liftIO $ SimpleSMT.assert solver expr
    return isTotal

assertNot ::
  (MonadIO m) =>
  Constraint ->
  SolverT s m Bool
assertNot c =
  SolverT $ ReaderT $ \solver -> do
    (isTotal, expr) <- constraintToSExpr c
    liftIO $ SimpleSMT.assert solver (SimpleSMT.not expr)
    return isTotal

atomicConstraintToSExpr :: Monad m
                    => AtomicConstraint -> ExceptT String m SimpleSMT.SExpr
atomicConstraintToSExpr (name :== term) =
  do
    let smtName = toSmtName name
    d <- translateTerm term
    return $ SimpleSMT.symbol smtName `SimpleSMT.eq` d
atomicConstraintToSExpr (Eq term1 term2) = do
  t1 <- translateTerm term1
  t2 <- translateTerm term2
  return $ t1 `SimpleSMT.eq` t2

-- Since the translation of atomic constraints can fail,
-- the translation of constraints does not always carry oll the information it could.
-- So the boolean indicates if some atomic constraints have been forgotten during the translation.
constraintToSExpr :: Monad m
                    => Constraint -> m (Bool, SimpleSMT.SExpr)
constraintToSExpr (And constraints) = do
  atomTrads <- mapM (runExceptT . atomicConstraintToSExpr) constraints
  return (all isRight atomTrads, SimpleSMT.andMany (rights atomTrads))
constraintToSExpr Bottom = return (True, SimpleSMT.bool False)

-- * Base defs

-- | Captures arbitrary types that can be translated to SMTLIB.
class (Show t) => ToSMT t where
  translate :: t -> SimpleSMT.SExpr

instance ToSMT Void where
  translate = absurd

-- | Prefix Pirouette names with "pir" to avoid name clashes with SMT builtins
toSmtName :: String -> String
toSmtName = ("s_" ++)

-- | Class for capturing solver specific functionality, enabling users to easily extend the
--  set of supported solvers.
class IsSolver s where
  launchSolver :: (MonadIO m) => m SimpleSMT.Solver

data CVC4_DBG

instance IsSolver CVC4_DBG where
  launchSolver = cvc4_ALL_SUPPORTED True

data CVC4

instance IsSolver CVC4 where
  launchSolver = cvc4_ALL_SUPPORTED True

-- | Prepare a CVC4 solver with all supported theories, which is necessary
-- to handle datatypes. The boolean parameter controls debug messages.
cvc4_ALL_SUPPORTED :: MonadIO m => Bool -> m SimpleSMT.Solver
cvc4_ALL_SUPPORTED dbg = do
  -- This generates a "Solver" which logs every interaction it has.
  -- To suppress this logging, replace the 2 next lines by
  -- s <- liiftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2"] Nothing
  ml <- if dbg then Just <$> liftIO (SimpleSMT.newLogger 0) else return Nothing
  s <- liftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] ml
  liftIO $ SimpleSMT.setLogic s "ALL_SUPPORTED"
  return s

-- * Translation of Terms

translateTerm :: (Monad m) => Term Var -> ExceptT String m SimpleSMT.SExpr
translateTerm (App v args) = mapM translateTerm args >>= translateVar v
translateTerm t@(Lam _ _) =
  throwError $ "Translate term to smtlib: Lambda abstraction in term: " ++ renderSingleLineStr (pretty t)

translateVar :: (Monad m) => Var -> [SimpleSMT.SExpr] -> ExceptT String m SimpleSMT.SExpr
translateVar (Symb s) [] = return $ SimpleSMT.symbol $ toSmtName s
translateVar (Free b) args = translateBuiltin b args
translateVar (Literal l) [] = translateLit l
translateVar v args =
  throwError $ "translateVar: unsupported: " ++ show v ++ " @ " ++ show args

translateLit :: (Monad m) => Lit -> m SimpleSMT.SExpr
translateLit (LitI i) = return $ SimpleSMT.int i
translateLit (LitB i) = return $ SimpleSMT.bool i

translateType :: (Monad m) => Type -> ExceptT String m SimpleSMT.SExpr
translateType TyInteger = return SimpleSMT.tInt
translateType TyBool = return SimpleSMT.tBool
translateType (TyFun _ _) = throwError "tranlsateType: translating a TyFun"

translateBuiltin :: (Monad m) => Builtin -> [SimpleSMT.SExpr] -> ExceptT String m SimpleSMT.SExpr
translateBuiltin BinAdd [x, y] = return $ SimpleSMT.add x y
translateBuiltin BinSub [x, y] = return $ SimpleSMT.sub x y
translateBuiltin BinLeq [x, y] = return $ SimpleSMT.leq x y
translateBuiltin BinEq  [x, y] = return $ SimpleSMT.eq x y
translateBuiltin BinIf  [x, y, z] = return $ SimpleSMT.ite x y z
translateBuiltin b args = throwError $ "translateBuiltin: wrong arity: " ++ show b ++ "@" ++ show args

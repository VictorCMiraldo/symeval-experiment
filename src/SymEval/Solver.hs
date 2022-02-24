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

module SymEval.Solver where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Concurrent.MVar
import Data.Bifunctor (bimap)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import qualified SimpleSMT
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Applicative
import Control.Parallel
import SymEval.Pretty
import Data.Void
import SymEval.Term
import Prettyprinter hiding (Pretty, pretty)
import Data.List (intersperse)
import GHC.IO.Unsafe (unsafePerformIO)
import Control.Exception (evaluate)

-- | SMT Constraints:
data Constraint
  = String :== Term Var
  | Eq (Term Var) (Term Var)
  | And [Constraint]
  | Bottom
  deriving (Eq , Show)

instance  Pretty Constraint where
  pretty (n :== term) =
    pretty n <+> "↦" <+> pretty term
  pretty (Eq t u) =
    pretty t <+> "==" <+> pretty u
  pretty Bottom =
    "⊥"
  pretty (And []) =
    "⊤"
  pretty (And l) =
    mconcat $ intersperse "\n∧ " (map pretty l)

instance Semigroup Constraint where
  (<>) = andConstr

instance Monoid Constraint where
  mempty = And []

andConstr :: Constraint -> Constraint -> Constraint
andConstr Bottom _ = Bottom
andConstr _ Bottom = Bottom
andConstr (And l) (And m) = And (l ++ m)
andConstr (And l) y = And (y : l)
andConstr x (And m) = And (x : m)
andConstr x y = And [x, y]

type Solver = M.Map String Type -> Constraint -> Bool

{-# NOINLINE solve #-}
solve :: String -> Solver
solve v = unsafePerformIO $ do
  solver <- cvc4_ALL_SUPPORTED True
  runSolverWith solver $ declareVariables (M.fromList [(v, TyBool)])
  mv <- evaluate solver >>= newMVar
  return $ \ env c -> unsafePerformIO $ do
    withMVar mv $ \safeSolver -> do
     runSolverWith safeSolver $ do
       solverPush
       declareVariables env
       assert env c
       res <- checkSat
       solverPop
       return $ case res of
         SimpleSMT.Unsat -> False
         _ -> True

runSolverWith :: (MonadIO m) => SimpleSMT.Solver -> SolverT s m a -> m a
runSolverWith solver (SolverT comp) = runReaderT comp solver


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
declareVariables :: (MonadIO m, MonadFail m) => M.Map String Type -> SolverT s m ()
declareVariables = mapM_ (uncurry declareVariable) . M.toList

-- | Declares a single variable in the current solver session.
declareVariable :: (MonadIO m, MonadFail m) => String -> Type -> SolverT s m ()
declareVariable varName varTy = do
  solver <- ask
  ty <- lift $ translateType varTy
  liftIO $ void $ SimpleSMT.declare solver (toSmtName varName) ty

-- | Asserts a constraint; check 'Constraint' for more information
assert ::
  (MonadIO m, MonadFail m) =>
  M.Map String Type ->
  Constraint ->
  SolverT s m ()
assert gamma c = SolverT $ ReaderT $ \solver -> assertConstraintRaw solver gamma c
  where
    assertConstraintRaw :: (MonadIO m, MonadFail m)
                        => SimpleSMT.Solver -> M.Map String Type -> Constraint -> m ()
    assertConstraintRaw s env (name :== term) =
      do
        let smtName = toSmtName name
        let (Just ty) = M.lookup name env
        d <- translateTerm term
        liftIO $ SimpleSMT.assert s (SimpleSMT.symbol smtName `SimpleSMT.eq` d)
    assertConstraintRaw s _ (Eq term1 term2) = do
      t1 <- translateTerm term1
      t2 <- translateTerm term2
      liftIO $ SimpleSMT.assert s (t1 `SimpleSMT.eq` t2)
    assertConstraintRaw s env (And constraints) =
      sequence_ (assertConstraintRaw s env <$> constraints)
    assertConstraintRaw s _ Bottom = liftIO $ SimpleSMT.assert s (SimpleSMT.bool False)

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
  launchSolver = cvc4_ALL_SUPPORTED False

-- | Prepare a CVC4 solver with all supported theories, which is necessary
-- to handle datatypes. The boolean parameter controls debug messages.
cvc4_ALL_SUPPORTED :: (MonadIO m) => Bool -> m SimpleSMT.Solver
cvc4_ALL_SUPPORTED dbg = do
  -- This generates a "Solver" which logs every interaction it has.
  -- To suppress this logging, replace the 2 next lines by
  -- s <- liiftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2"] Nothing
  ml <- if dbg then Just <$> liftIO (SimpleSMT.newLogger 0) else return Nothing
  s <- liftIO $ SimpleSMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] ml
  liftIO $ SimpleSMT.setLogic s "ALL_SUPPORTED"
  return s

-- * Translation of Terms

translateTerm :: (MonadFail m) => Term Var -> m SimpleSMT.SExpr
translateTerm (App var args) = mapM translateTerm args >>= translateVar var
translateTerm t@(Lam _ _) =
  fail $ "Translate term to smtlib: Lambda abstraction in term: " ++ renderSingleLineStr (pretty t)

translateVar :: (MonadFail m) => Var -> [SimpleSMT.SExpr] -> m SimpleSMT.SExpr
translateVar (Symb s) [] = return $ SimpleSMT.symbol $ toSmtName s
translateVar (Free b) args = translateBuiltin b args
translateVar (Literal l) [] = translateLit l
translateVar v args =
  fail $ "translateVar: unsupported: " ++ show v ++ " @ " ++ show args

translateLit :: (MonadFail m) => Lit -> m SimpleSMT.SExpr
translateLit (LitI i) = return $ SimpleSMT.int i
translateLit (LitB i) = return $ SimpleSMT.bool i

translateType :: (MonadFail m) => Type -> m SimpleSMT.SExpr
translateType TyInteger = return SimpleSMT.tInt
translateType TyBool = return SimpleSMT.tBool
translateType (TyFun _ _) = fail "tranlsateType: translating a TyFun"

translateBuiltin :: (MonadFail m) => Builtin -> [SimpleSMT.SExpr] -> m SimpleSMT.SExpr
translateBuiltin BinAdd [x, y] = return $ SimpleSMT.add x y
translateBuiltin BinSub [x, y] = return $ SimpleSMT.sub x y
translateBuiltin BinMul [x, y] = return $ SimpleSMT.mul x y
translateBuiltin BinLeq [x, y] = return $ SimpleSMT.leq x y
translateBuiltin BinEq  [x, y] = return $ SimpleSMT.eq x y
translateBuiltin BinIf  [x, y, z] = return $ SimpleSMT.ite x y z
translateBuiltin b args = fail $ "translateBuiltin: wrong arity: " ++ show b ++ "@" ++ show args

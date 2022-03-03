{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SymEval where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import qualified Data.Map.Strict as Map
import Prettyprinter hiding (Pretty (..))
import ListT (ListT)
import qualified ListT

import SymEval.Term
import SymEval.Pretty
import SymEval.Solver
import qualified SimpleSMT

data PathStatus = Completed | OutOfFuel

data Path res = Path
  { pathConstraint :: Constraint,
    pathGamma :: Map.Map String Type,
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

data SymEvalSt = SymEvalSt
  { sestConstraint :: Constraint,
    sestGamma :: Map.Map String Type,
    sestFreshCounter :: Int,
    sestFuel :: Int,
    -- |A branch that has been validated before is never validated again /unless/ we 'learn' something new.
    sestValidated :: Bool
  }

-- |Given a result and a resulting state, returns a 'Path' representing it.
path :: a -> SymEvalSt -> Path a
path x st = Path
  { pathConstraint = sestConstraint st
  , pathGamma = sestGamma st
  , pathStatus = if sestFuel st <= 0 then OutOfFuel else Completed
  , pathResult = x
  }

-- | Our default solver; maybe this should become a type-level parm too...
type Sol = CVC4

-- | A 'SymEvalT' is equivalent to a function with type:
--
-- > SymEvalSt -> SMT.Solver -> m [(a, SymEvalSt)]
newtype SymEvalT m a = SymEvalT {symEvalT :: StateT SymEvalSt (SolverT Sol (ListT m)) a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadState SymEvalSt)

symevalT :: (MonadIO m) => SymEvalT m a -> m [Path a]
symevalT = runSymEvalT st0
  where
    st0 = SymEvalSt mempty Map.empty 0 10 False

runSymEvalTRaw :: (Monad m) => SymEvalSt -> SymEvalT m a -> SolverT Sol (ListT m) (a, SymEvalSt)
runSymEvalTRaw st = flip runStateT st . symEvalT

-- |Running a symbolic execution will prepare the solver only once, then use a persistent session
-- to make all the necessary queries.
runSymEvalT :: (MonadIO m) => SymEvalSt -> SymEvalT m a -> m [Path a]
runSymEvalT st = ListT.toList . fmap (uncurry path) . runSolverT . runSymEvalTRaw st

instance (Monad m) => Alternative (SymEvalT m) where
  empty = SymEvalT $ StateT $ const empty
  xs <|> ys = SymEvalT $ StateT $ \st -> runSymEvalTRaw st xs <|> runSymEvalTRaw st ys

instance MonadTrans SymEvalT where
  lift = SymEvalT . lift . lift . lift

instance (MonadIO m) => MonadIO (SymEvalT m) where
  liftIO = lift . liftIO

pathIsPlausible :: (MonadIO m) => SymEvalSt -> SolverT Sol m Bool
pathIsPlausible env
  | sestValidated env = return True -- We already validated this branch before; nothing new was learnt.
  | otherwise = do
      solverPush
      decl <- runExceptT (declareVariables (sestGamma env))
      case decl of
        Right _ -> return ()
        Left s -> error s
      void $ assert (sestConstraint env)
      res <- checkSat
      solverPop
      return $ case res of
        SimpleSMT.Unsat -> False
        _ -> True

checkProperty :: (MonadIO m) => Constraint -> Constraint -> SymEvalSt -> SolverT Sol m SimpleSMT.Result
checkProperty cOut cIn env = do
  solverPush
  decl <- runExceptT (declareVariables (sestGamma env))
  case decl of
    Right _ -> return ()
    Left s -> error s
  b1 <- assert (sestConstraint env)
  b2 <- assert cOut
  b3 <- assertNot cIn
  result <- checkSat
  solverPop
  case result of
    SimpleSMT.Sat ->
      if b1 && b2 && b3
      then return SimpleSMT.Sat
      -- If a partial translation of the constraint is SAT,
      -- it does not guarantee us that the full set of constraints is satisfiable.
      else return SimpleSMT.Unknown
    _ -> return result


-- |Prune the set of paths in the current set.
prune :: forall m a . (MonadIO m) => SymEvalT m a -> SymEvalT m a
prune xs = SymEvalT $ StateT $ \st -> do
    (x, st') <- runSymEvalTRaw st xs
    ok <- pathIsPlausible st'
    guard ok
    return (x, st')

-- | Prune the set of paths in the current set.
pruneAndValidate :: forall m . (MonadIO m) => Constraint -> Constraint -> SymEvalT m Bool
pruneAndValidate cOut cIn =
  SymEvalT $ StateT $ \st -> do
    pathOk <- pathIsPlausible st
    guard pathOk
    contradictProperty <- checkProperty cOut cIn st
    case contradictProperty of
      SimpleSMT.Unsat -> empty
      SimpleSMT.Sat -> return (False, st)
      SimpleSMT.Unknown -> return (True, st)

-- |Learn a new constraint and add it as a conjunct to the set of constraints of
-- the current path. Make sure that this branch gets marked as /not/ validated, regardless
-- of whether or not we had already validated it before.
learn :: (MonadIO m) => Constraint -> SymEvalT m ()
learn c = modify (\st -> st { sestConstraint = c <> sestConstraint st, sestValidated = False })

declSymVars :: (MonadIO m) => [(String, Type)] -> SymEvalT m [String]
declSymVars vs = do
  modify (\st -> st { sestGamma = Map.union (sestGamma st) (Map.fromList vs) })
  return $ map fst vs

freshSymVar :: (MonadIO m) => Type -> SymEvalT m String
freshSymVar ty = head <$> freshSymVars [ty]

freshSymVars :: (MonadIO m) => [Type] -> SymEvalT m [String]
freshSymVars [] = return []
freshSymVars tys = do
  let n = length tys
  ctr <- gets sestFreshCounter
  modify (\st -> st { sestFreshCounter = sestFreshCounter st + n })
  let vars = zipWith (\i ty -> ("sv" ++ show i , ty)) [ctr..] tys
  declSymVars vars

runEvaluation :: (MonadIO m) => Term Var -> SymEvalT m (Term Var)
runEvaluation t = do
  liftIO $ putStrLn $ "evaluating: " ++ show (pretty t)
  let (lams, _) = getHeadLams t
  svars <- freshSymVars lams
  symeval (appN t $ map (var . Symb) svars)

consumeGas :: (MonadIO m) => SymEvalT m ()
consumeGas = modify (\st -> st { sestFuel = sestFuel st - 1 })

currentGas :: (MonadIO m) => SymEvalT m Int
currentGas = gets sestFuel

symeval :: (MonadIO m) => Term Var -> SymEvalT m (Term Var)
symeval t = do
  fuelLeft <- currentGas
  if fuelLeft <= 0
    then return t
    else prune $ symeval' t

symeval' :: (MonadIO m) => Term Var -> SymEvalT m (Term Var)
symeval' t@(Lam ty _) = do
  svar <- freshSymVar ty
  symeval' $ t `app` var (Symb svar)
symeval' u@(App hd args) = do
  case hd of
    Free BinIf -> do
      let [c, t, e] = args
      c' <- symeval' c
      asum
        [ do
            constr <- unifyLit c' (LitB True)
            learn constr
            consumeGas
            symeval t
        , do
            constr <- unifyLit c' (LitB False)
            learn constr
            consumeGas
            symeval e
        ]
    Free BinFix -> do
      let (f:rest) = args
      consumeGas
      symeval $ f `appN` (App (Free BinFix) [f] : rest)
    Free _ ->
      App hd <$> mapM symeval args
    _ -> return u

newtype OutCond = OutCond (Term Var -> Constraint)
newtype InCond = InCond Constraint

data EvaluationWitness =
  Verified | CounterExample (Term Var)

runConditionalEval :: (MonadIO m) => Term Var -> OutCond -> InCond -> SymEvalT m EvaluationWitness
runConditionalEval t (OutCond q) (InCond p) = do
  liftIO $ putStrLn $ "Conditionally evaluating: " ++ show (pretty t)
  conditionalEval t q p

conditionalEval :: (MonadIO m) => Term Var -> (Term Var -> Constraint) -> Constraint -> SymEvalT m EvaluationWitness
conditionalEval t outCond inCond = do
  toEvaluateMore <- pruneAndValidate (outCond t) inCond
  if toEvaluateMore
  then do
    t' <- symEvalOneStep t
    conditionalEval t' outCond inCond
  else
    return (CounterExample t)

symEvalOneStep :: (MonadIO m) => Term Var -> SymEvalT m (Term Var)
symEvalOneStep t =
  case t of
    App v args -> case v of
      Free BinFix -> do
        let (f:rest) = args
        return (f `appN` (App (Free BinFix) [f] : rest))
      Free BinIf -> do
        let [cond, caseT, caseF] = args
        cond' <- symEvalOneStep cond
        if cond == cond'
        then
          asum
            [ do
                constr <- unifyLit cond (LitB True)
                learn constr
                return caseT
            , do
                constr <- unifyLit cond (LitB False)
                learn constr
                return caseF
            ]
        else
          return $ App (Free BinIf) [cond', caseT, caseF]
      _ -> App v <$> mapM symEvalOneStep args
    Lam ty _ -> do
      svar <- freshSymVar ty
      Lam ty <$> symEvalOneStep (t `app` var (Symb svar))

unifyLit :: (Monad m) => Term Var -> Lit -> SymEvalT m Constraint
unifyLit (App (Symb s) []) l = return $ And [s :== App (Literal l) []]
unifyLit (App (Literal l') []) l = guard (l' == l) >> return mempty
unifyLit t l = return $ And [Eq t (App (Literal l) [])]

--- TMP CODE

instance (Pretty a) => Pretty (Path a) where
  pretty (Path conds gamma ps res) =
    vsep [ "With:" <+> pretty (Map.toList gamma)
         , "If:" <+> indent 2 (pretty conds)
         , "Status:" <+> pretty ps
         , "Result:" <+> indent 2 (pretty res)
         ]

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

instance Pretty EvaluationWitness where
  pretty Verified = "Verified"
  pretty (CounterExample t) = "COUNTER-EXAMPLE: The result is" <+> pretty t

runFor :: (MonadIO m) => [(String, Type)] -> Term Var -> OutCond -> InCond -> m ()
runFor args t outCond inCond = do
  paths <- symevalT $ do
    argNames <- declSymVars args
    let tApplied = t `appN` map (var . Symb) argNames
    runConditionalEval tApplied outCond inCond
  mapM_ (liftIO . print . pretty) paths

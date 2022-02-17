module Main where

import GHC.IO.Encoding

import SymEval
import SymEval.Term

-- smart constructors for builtin terms:

fix :: Term Var -> Term Var
fix f = App (Free BinFix) [f]

ite :: Term Var -> Term Var -> Term Var -> Term Var
ite c t e = App (Free BinIf) [c, t, e]

(.==) :: Term Var -> Term Var -> Term Var
t .== u = App (Free BinEq) [t, u]

add :: Term Var -> Term Var -> Term Var
add t u = App (Free BinAdd) [t, u]

sub :: Term Var -> Term Var -> Term Var
sub t u = App (Free BinSub) [t, u]

litI :: Integer -> Term Var
litI = flip App [] . Literal . LitI

fib :: Term Var
fib = fix $ Lam (TyFun TyInteger TyInteger) $ Lam TyInteger $
  let n = var $ Bound 0
      f = Bound 1
   in ite (n .== litI 0)
          (litI 1)
          (ite (n .== litI 1)
               (litI 1)
               (add (App f [sub n (litI 1)]) (App f [sub n (litI 2)])))

main :: IO ()
main = do
  setLocaleEncoding utf8
  runFor fib

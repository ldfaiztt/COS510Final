{-
Syntax and Implementation of Boolean Expressions
================================================
-}

module BoolExp where

import Pi
import qualified Data.Map.Strict as M 

data BoolExp
  = BVar Name
  | BVal Bool
  | BoolExp :&&: BoolExp
  | BoolExp :||: BoolExp
  | Not BoolExp
  deriving Show

-- Environments for interpreting boolean expressions
type BEnv = M.Map Name Bool

-- TASK!
-- compile_b tchan fchan b
-- returns a process p that when juxtaposed with a compatible environment
-- sends a message on tchan if the boolean expression evaluates to true
-- sends a message on fchan if the boolean expression evaluates to false
compile_b :: Name -> Name -> BoolExp -> Pi
compile_b tchan fchan (BVal True) = Out tchan unitE
compile_b tchan fchan (BVal False) = Out fchan unitE
compile_b tchan fchan (BVar var) = (Out req unitE)
                         :|: (Inp tch unitP $ Out tchan unitE)
                         :|: (Inp fch unitP $ Out fchan unitE)
                         where req = var ++ "req"
                               tch = var ++ "tch"
                               fch = var ++ "fch"
compile_b tchan fchan (Not b) = compile_b fchan tchan b
compile_b tchan fchan (b1 :&&: b2) =
    New b1t unitT $
    New b1f unitT $
    New b2t unitT $
    New b2f unitT $
    (compile_b b1t b1f b1) :|: (compile_b b2t b2f b2)
    :|: (Inp b1t unitP $ (Inp b2t unitP $ Out tchan unitE)
                               :|: (Inp b2f unitP $ Out fchan unitE))
    :|: (Inp b1f unitP $ Out fchan unitE)
    where b1t = tchan ++ fchan ++ "1t"
          b1f = tchan ++ fchan ++ "1f"
          b2t = tchan ++ fchan ++ "2t"
          b2f = tchan ++ fchan ++ "2f"
compile_b tchan fchan (b1 :||: b2) =
    New b1t unitT $
    New b1f unitT $
    New b2t unitT $
    New b2f unitT $
    (compile_b b1t b1f b1) :|: (compile_b b2t b2f b2)
    :|: (Inp b1t unitP $ Out tchan unitE)
    :|: (Inp b1f unitP $ (Inp b2t unitP $ Out tchan unitE)
                               :|: (Inp b2f unitP $ Out fchan unitE))
    where b1t = tchan ++ fchan ++ "1t"
          b1f = tchan ++ fchan ++ "1f"
          b2t = tchan ++ fchan ++ "2t"
          b2f = tchan ++ fchan ++ "2f"
  

-- TASK!
-- compile a boolean variable environment into a process that
-- communicates with a compiled Boolean expression containing free
-- variables from the environment
compile_benv :: BEnv -> Pi -> Pi
compile_benv benv p = M.foldrWithKey fenv p benv

fenv :: Name -> Bool -> Pi -> Pi
fenv var val pi1 = pi1 :|: pi
    where req = var ++ "req"
          tch = var ++ "tch"
          fch = var ++ "fch"
          pinext = if val then Out tch unitE else Out fch unitE
          pi =  New req unitT $
                New tch unitT $
                New fch unitT $
                RepInp req unitP pinext

start_bool :: BEnv -> BoolExp -> IO ()
start_bool benv bexp = 
  start pi
    where
      tchan = "t"
      fchan = "f"   
      pi = New tchan unitT $ 
           New fchan unitT $ 
           compile_benv benv (compile_b tchan fchan bexp) :|:
           Inp tchan unitP (printer "true") :|:
           Inp fchan unitP (printer "false")
           

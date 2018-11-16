{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, ExistentialQuantification #-}
module Monopig1 where

import Prelude hiding (log)
import Data.Semigroup (Max(..),stimes)
import Data.Monoid
import Data.Vector ((//),(!),Vector)
import qualified Data.Vector as V (replicate)

------------------------------------------------------------
-- The machine

type Stack = [Int]
type Memory = Vector Int

data VM = VM { stack :: Stack
             , status :: Maybe String
             , memory :: Memory }
        deriving Show

type Processor = VM -> VM

memSize = 4
mkVM = VM mempty mempty (V.replicate memSize 0)

setStack :: Stack -> Processor
setStack  x (VM _ st m) = VM x st m

setStatus :: Maybe String -> Processor
setStatus st (VM s _ m) = VM s st m

setMemory :: Memory -> Processor
setMemory m (VM s st _) = VM s st m

------------------------------------------------------------
-- The action monoid

newtype Action a = Action { runAction :: a -> a }

instance Semigroup (Action a) where
  Action f <> Action g = Action (g . f)

instance Monoid (Action a) where
  mempty = Action id

------------------------------------------------------------
-- The Program

newtype Program = Program { getProgram :: Action VM }
  deriving (Semigroup, Monoid)

program :: (Stack -> Processor) -> Program
program f = Program . Action $
  \vm -> case status vm of
    Nothing -> f (stack vm) vm
    m -> vm

programM :: ((Memory,Stack) -> Processor) -> Program
programM f = Program . Action $
  \vm -> case status vm of
    Nothing -> f (memory vm, stack vm) vm
    m -> vm

run = runAction . getProgram

------------------------------------------------------------
-- basic programs (commands)

err m = setStatus . Just $ "Error : " ++ m

-- stack manipulation

pop = program $ 
  \case x:s -> setStack s
        _ -> err "pop expected an argument."

push x = program $ \s -> setStack (x:s)

dup = program $ 
  \case x:s -> setStack (x:x:s)
        _ -> err "dup expected an argument."

swap = program $ 
  \case x:y:s -> setStack (y:x:s)
        _ -> err "swap expected two arguments."

exch = program $ 
  \case x:y:s -> setStack (y:x:y:s)
        _ -> err "expected two arguments."

-- memory access

put i = indexed i $
    \case (m, x:s) -> setStack s . setMemory (m // [(i,x)])
          _ -> err "put expected an argument"

get i = indexed i $ \(m, s) -> setStack ((m ! i) : s)

indexed :: Int -> ((Memory, Stack) -> Processor) -> Program
indexed i f = programM $
  if (i < 0 || i >= memSize)
  then const $ err $ "index in within 0 and " ++ show memSize
  else f

-- arythmetic

unary n f = program $
  \case x:s -> setStack (f x:s)
        _ -> error $ "operation " ++ show n ++ " expected an argument"

binary n f = program $
  \case x:y:s -> setStack (f x y:s)
        _ -> error $ "operation " ++ show n ++ " expected two arguments"

add = binary "add" (+)
sub = binary "sub" (flip (-))
mul = binary "mul" (*)
frac = binary "frac" (flip div)
modulo = binary "modulo" (flip mod)
neg = unary "neg" (\x -> -x)
inc = unary "inc" (\x -> x+1)
dec = unary "dec" (\x -> x-1)
eq = binary "eq" (\x -> \y -> if (x == y) then 1 else 0)
neq = binary "neq" (\x -> \y -> if (x /= y) then 1 else 0)
lt = binary "lt" (\x -> \y -> if (x > y) then 1 else 0)
gt = binary "gt" (\x -> \y -> if (x < y) then 1 else 0)

-- branching and cycling combinators

proceed :: Program -> Stack -> Processor
proceed prog s = run prog . setStack s

rep body = program go
  where go (n:s) = proceed (stimes n body) s
        go _ = err "rep expected an argument."

branch br1 br2 = program go
   where go (x:s) = proceed (if (x /= 0) then br1 else br2) s
         go _ = err "branch expected an argument."

while test body = program (const go)
  where go vm = let res = proceed test (stack vm) vm
          in case (stack res) of
               0:s -> proceed mempty s res
               _:s -> go $ proceed body s res
               _ -> err "while expected an argument." vm

------------------------------------------------------------
-- Example programs

-- run (push 5 <> dup <> add) mkVM
-- run (push 5 <> fact) mkVM


fact = dup <> push 2 <> lt <>
       branch (push 1) (dup <> dec <> fact) <>
       mul

fact1 = push 1 <> swap <>
        while (dup <> push 1 <> gt)
        (
          swap <> exch <> mul <> swap <> dec
        ) <>
        pop

range = exch <> sub <> dup<> push 0 <> gt <>
        branch (rep (dup <> inc)) (neg <> rep (dup <> dec))

fact2 = inc <> push 1 <> swap <> range <> dec <> dec <> rep mul

fact3 = dup <> put 0 <> dup <> dec <>
        rep
        (
          dec <> dup <> get 0 <> mul <> put 0
        ) <>
        get 0 <> swap <> pop

copy2 = exch <> exch

gcd1 = while (copy2 <> neq)
       (
         copy2 <> lt <> branch mempty swap <> exch <> sub
       ) <>
       pop

range1 = exch <> sub <> rep (dup <> inc)

pow = swap <> put 0 <> push 1 <> put 1 <>
      while (dup <> push 0 <> gt)
      (
        dup <> push 2 <> modulo <>
        branch (dec <> get 0 <> dup <> get 1 <> mul <> put 1) (get 0) <>
        dup <> mul <> put 0 <>
        push 2 <> frac
      ) <>
      pop <> get 1

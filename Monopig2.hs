{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, ExistentialQuantification 
#-}
module Monopig2 where

import Data.Semigroup (Max(..),stimes)
import Data.Monoid
import Data.Vector ((//),(!),Vector)
import qualified Data.Vector as V (replicate)
import Data.Foldable

------------------------------------------------------------
-- The machine

type Stack = [Int]
type Memory = Vector Int

data VM a = VM { stack :: Stack
               , status :: Maybe String
               , memory :: Memory
               , journal :: a }
            deriving Show

memSize = 4
mkVM = VM mempty mempty (V.replicate memSize 0)

setStack  x (VM _ st m j) = VM x st m j
setStatus st (VM s _ m j) = VM s st m j
setMemory m (VM s st _ j) = VM s st m j
addRecord x (VM s st m j) = VM s st m (x<>j)

------------------------------------------------------------
-- The action monoid

newtype Action a = Action { runAction :: a -> a }

instance Semigroup (Action a) where
  Action f <> Action g = Action (g . f)

instance Monoid (Action a) where
  mempty = Action id

------------------------------------------------------------
-- The Program abstraction

newtype Program a = Program { getProgram :: Action (VM a) }
  deriving (Semigroup, Monoid)

program f p = Program . Action $
  \vm -> case status vm of
    Nothing -> p . (f (stack vm)) $ vm
    m -> vm

programM f p = Program . Action $
  \vm -> case status vm of
    Nothing -> p . (f (memory vm, stack vm)) $ vm
    m -> vm

run = runAction . getProgram

------------------------------------------------------------
-- executors

exec prog = run (prog id) (mkVM ())

execLog p prog = run (prog $ \vm -> addRecord (p vm) vm) (mkVM mempty)

f &&& g = \r -> (f r, g r)
  
logStack vm   = [stack vm]
logStackUsed  = Max . length . stack
logSteps      = const (Sum 1)

logMemoryUsed :: VM a -> Max Int
logMemoryUsed = Max . getSum . count . memory
  where count = foldMap (\x -> if x == 0 then 0 else 1)

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

indexed i f = programM $ if (i < 0 || i >= memSize)
                         then const $ err "index in [0,16]"
                         else f

-- arythmetic

unary n f = program $
  \case x:s -> setStack (f x:s)
        _ -> err $ "operation " ++ show n ++ " expected an argument"

binary n f = program $
  \case x:y:s -> setStack (f x y:s)
        _ -> err $ "operation " ++ show n ++ " expected two arguments"

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

proceed p prog s = run (prog p) . setStack s

rep body p = program go id
  where go (n:s) = proceed p (stimes n body) s
        go _ = err "rep expected an argument."

branch br1 br2 p = program go id
   where go (x:s) = proceed p (if (x /= 0) then br1 else br2) s
         go _ = err "branch expected an argument."

while test body p = program (const go) id
  where go vm = let res = proceed p test (stack vm) vm
          in case (stack res) of
               0:s -> proceed p mempty s res
               _:s -> go $ proceed p body s res
               _ -> err "while expected an argument." vm

------------------------------------------------------------
-- Example programs

-- exec (push 5 <> dup <> add)
-- execLog logStack (push 5 <> fact)
-- journal $ execLog (logStack &&& logSteps) (push 5 <> fact)

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

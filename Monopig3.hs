{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, TupleSections,BangPatterns  #-}

module Main where

import Data.Semigroup (Max(..),stimes, Semigroup(..))
import Data.Monoid hiding ((<>))
import Data.Vector ((//), (!), Vector,  toList)
import qualified Data.Vector as V (replicate)
import Data.List.Split
import Data.List (inits, tails, intercalate)

------------------------------------------------------------
-- The machine

type Stack = [Int]
type Memory = Vector Int

data VM a = VM { stack :: !Stack
               , status :: Maybe String
               , memory :: !Memory
               , journal :: a }
            deriving Show

memSize = 650
mkVM = VM mempty mempty (V.replicate memSize 0)

setStack  x (VM _ st m l) = VM x st m l
setStatus st (VM s _ m l) = VM s st m l
setMemory m (VM s st _ l) = VM s st m l
addRecord x (VM s st m l) = VM s st m (x<>l)

------------------------------------------------------------
-- The action monoid

newtype Action a = Action { runAction :: a -> a }

instance Semigroup (Action a) where
  Action f <> Action g = Action (g . f)

instance Monoid (Action a) where
  mempty = Action id

------------------------------------------------------------
-- The Code abstraction

data Code = IF [Code] [Code]
          | REP [Code]
          | WHILE [Code] [Code]
          | PUT Int | GET Int
          | PUSH Int | POP | DUP | SWAP | EXCH
          | INC | DEC | NEG
          | ADD | MUL | SUB | DIV | MOD
          | EQL | LTH | GTH | NEQ
          deriving (Read, Show, Eq)

------------------------------------------------------------
-- The Program abstraction

newtype Program a = Program { getProgram :: ([Code], Action (VM a)) }
  deriving (Semigroup, Monoid)

type Program' j = (Code -> VM j -> VM j) -> Program j

program c f p = Program . ([c],) . Action $
  \vm -> case status vm of
    Nothing -> p c . (f (stack vm)) $ vm
    m -> vm

programM c f p = Program . ([c],) . Action $
  \vm -> case status vm of
    Nothing -> p c . (f (memory vm, stack vm)) $ vm
    m -> vm

run = runAction . snd . getProgram

nop = const id

toCode prog = fst . getProgram $ prog nop

------------------------------------------------------------
-- executors

exec prog = run (prog nop) (mkVM ())

execLog p prog = run (prog $ \c -> \vm -> addRecord (p c vm) vm) (mkVM mempty)

debug :: Program' [String] -> String
debug = unlines . reverse . journal . execLog logRun

f &&& g = \c -> \r -> (f c r, g c r)

logStack _ vm   = [stack vm]
logStackUsed _ = Max . length . stack
logSteps _     = const (Sum 1)
logCode c _   = [c]
logRun com vm = [pad 10 c ++ "| " ++ pad 20 s ++ "| " ++ m]
  where c = show com
        m = unwords $ show <$> toList (memory vm)
        s = unwords $ show <$> stack vm
        pad n x = take n (x ++ repeat ' ')

------------------------------------------------------------
-- basic programs (commands)

err m = setStatus . Just $ "Error : " ++ m

-- stack manipulation

pop = program POP $ 
  \case x:s -> setStack s
        _ -> err "pop expected an argument."

push x = program (PUSH x) $ \s -> setStack (x:s)

dup = program DUP $ 
  \case x:s -> setStack (x:x:s)
        _ -> err "dup expected an argument."

swap = program SWAP $ 
  \case x:y:s -> setStack (y:x:s)
        _ -> err "swap expected two arguments."

exch = program EXCH $ 
  \case x:y:s -> setStack (y:x:y:s)
        _ -> err "expected two arguments."

-- memory access

put i = indexed (PUT i) i $
    \case (m, x:s) -> setStack s . setMemory (m // [(i,x)])
          _ -> err "put expected an argument"

get i = indexed (GET i) i $ \(m, s) -> setStack ((m ! i) : s)

indexed c i f = programM c $ if (i < 0 || i >= memSize)
                             then const $ err "index in [0,16]"
                             else f

-- arythmetic

unary c f = program c $
  \case x:s -> setStack (f x:s)
        _ -> err $ "operation " ++ show c ++ " expected an argument"

binary c f = program c $
  \case x:y:s -> setStack (f x y:s)
        _ -> err $ "operation " ++ show c ++ " expected two arguments"

add = binary ADD (+)
sub = binary SUB (flip (-))
mul = binary MUL (*)
frac = binary DIV (flip div)
modulo = binary MOD (flip mod)
neg = unary NEG (\x -> -x)
inc = unary INC (\x -> x+1)
dec = unary DEC (\x -> x-1)
eq = binary EQL (\x -> \y -> if (x == y) then 1 else 0)
neq = binary NEQ (\x -> \y -> if (x /= y) then 1 else 0)
lt = binary LTH (\x -> \y -> if (x > y) then 1 else 0)
gt = binary GTH (\x -> \y -> if (x < y) then 1 else 0)

-- branching and cycling combinators

proceed p prog s = run (prog p) . setStack s

rep body p = program (REP (toCode body)) go nop
  where go (n:s) = if n >= 0
                   then proceed p (stimes n body) s
                   else err "rep expected positive argument."
        go _ = err "rep expected an argument."

branch br1 br2 p = program (IF (toCode br1) (toCode br2)) go nop
   where go (x:s) = proceed p (if (x /= 0) then br1 else br2) s
         go _ = err "branch expected an argument."

while test body p = program (WHILE (toCode test) (toCode body)) (const go) nop
  where go vm = let res = proceed p test (stack vm) vm
          in case (stack res) of
               0:s -> proceed p mempty s res
               _:s -> go $ proceed p body s res
               _ -> err "while expected an argument." vm

------------------------------------------------------------
-- homomorpism: Code -> Program

fromCode = hom
  where
    hom = foldMap $  
      \case
        IF b1 b2 -> branch (hom b1) (hom b2)
        REP p -> rep (hom p)
        WHILE t b -> while (hom t) (hom b)
        PUT i -> put i
        GET i -> get i
        PUSH i -> push i
        POP -> pop
        DUP -> dup
        SWAP -> swap
        EXCH -> exch
        INC -> inc
        DEC -> dec
        ADD -> add
        MUL -> mul
        SUB -> sub
        DIV -> frac
        MOD -> modulo
        EQL -> eq
        LTH -> lt
        GTH -> gt
        NEQ -> neq
        NEG -> neg

------------------------------------------------------------
-- homomorpism: Program -> Arity

infix 7 :>

data Arity = Int :> Int
  deriving (Show,Eq)

instance Semigroup Arity where
  i1 :> o1 <> i2 :> o2 = let a = i1 `max` (i2 - o1 + i1)
                         in a :> (a + o1 - i1 + o2 - i2)

instance Monoid Arity where
  mappend = (<>)
  mempty = 0 :> 0

arity = hom . toCode
  where
    hom = foldMap $
      \case
        IF b1 b2 -> let i1:>o1 = hom b1
                        i2:>o2 = hom b2
                    in 1:>0 <> i1 `max` i2 :> o1 `min` o2
        REP p -> 1:>0
        WHILE t b -> hom t <> 1:>0
        PUT _ -> 1:>0
        GET _ -> 0:>1
        PUSH _ -> 0:>1
        POP -> 1:>0
        DUP -> 1:>2
        SWAP -> 2:>2
        EXCH -> 2:>3
        INC -> 1:>1
        DEC -> 1:>1
        NEG -> 1:>1
        _   -> 2:>1


arityTest = mapM_ print $
  [ 1:>2 <> 2:>3 == 1:>3
  , 0:>1 <> 1:>0 == 0:>0
  , 1:>0 <> 1:>0 == 2:>0
  , 1:>0 <> 2:>0 == 3:>0
  , 2:>0 <> 2:>0 == 4:>0
  , 1:>1 <> 1:>0 == 1:>0
  , 1:>1 <> 2:>0 == 2:>0
  , 2:>1 <> 2:>1 == 3:>1
  , 1:>0 <> 0:>1 == 1:>1
  , 1:>0 <> 1:>1 == 2:>1
  , 1:>1 <> 1:>0 == 1:>0
  , 1:>1 <> 1:>1 == 1:>1
  , 3:>0 <> 1:>1 == 4:>1
  , 0:>1 <> 0:>1 == 0:>2
  , 2:>3 <> 2:>3 == 2:>4
  , 1:>1 <> 3:>0 == 3:>0
  , 1:>3 <> 1:>3 == 1:>5
  , 0:>1 <> 2:>1 == 1:>1
  ]

------------------------------------------------------------
-- pretty printing as a homomorpism: Program -> String

listing = unlines . printCode 0 . toCode
  where
    printCode n = foldMap f
      where
        f = \case
          IF b1 b2 -> print "IF" <> indent b1 <> print ":" <> indent b2
          REP p -> print "REP" <> indent p
          WHILE t b -> print "WHILE" <> indent t <> indent b
          c -> print $ show c

        print x = [stimes n "  " ++ x]
        indent = printCode (n+1)

------------------------------------------------------------
-- memory requirements as a homomorpism: Program -> Max Int

memoryUse :: Program' a -> Max Int
memoryUse = memoryUse' . toCode
  where
    memoryUse' = foldMap $
      \case
        IF b1 b2 -> memoryUse' b1 <> memoryUse' b2
        REP p -> memoryUse' p
        WHILE t b -> memoryUse' t <> memoryUse' b
        PUT i -> Max (i+1)
        GET i -> Max (i+1)
        _ -> 0

------------------------------------------------------------
-- reduction using homomorphisms : `arity` and `memoryUse`

isReducible p = let p' = fromCode p
                in case arity p' of
                     0:>_ -> memoryUse p' == 0
                     _    -> False

reducible = go [] . toCode
  where go res [] = reverse res
        go res (p:ps) = if isReducible [p]
                        then let (a,b) = spanBy isReducible (p:ps)
                             in go (a:res) b
                        else go res ps

spanBy test l = case foldMap tst $ zip (inits l) (tails l) of
                  Last Nothing -> ([],l)
                  Last (Just x) -> x
  where tst x = Last $ if test (fst x) then Just x else Nothing 


reduce p = fromCode . process (reducible p) . toCode $ p
  where
    process = appEndo . foldMap (\x -> Endo $ x `replaceBy` shrink x)
    shrink = toCode . foldMap push . reverse . stack . exec . fromCode
    replaceBy x y = intercalate y . splitOn x

------------------------------------------------------------
-- Example programs

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

test = push 8 <>
       dup <> fact1 <> swap <>
       dup <> fact2 <> swap <>
       dup <> fact3 <> swap <>
       push 54 <> gcd1 <>
       dup <> push 20 <> pow

       
main = print $ stack $ exec sieve

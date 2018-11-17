{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, TupleSections #-}

module Main where

import Data.Monoid hiding ((<>))
import Data.Semigroup (Semigroup(..),stimes,Max(..))
import Data.Vector.Unboxed ((//),(!),Vector,toList)
import qualified Data.Vector.Unboxed as V (replicate)
import Data.List.Split
import Data.List (inits, tails, intercalate)
import Control.Monad
import Control.Monad.Identity

type Stack = [Int]
type Memory = Vector Int

memSize = 65000 :: Int

data VM a = VM { stack :: Stack
               , status :: Maybe String
               , memory :: Memory
               , journal :: a }
--            deriving Show

mkVM = VM mempty mempty (V.replicate memSize 0)

setStack  x (VM _ st m l) = return $ VM x st m l
setStatus st (VM s _ m l) = return $ VM s st m l
setMemory m (VM s st _ l) = return $ VM s st m l
addRecord x (VM s st m l) = VM s st m (x<>l)

------------------------------------------------------------

data Code = IF [Code] [Code]
          | REP [Code]
          | WHILE [Code] [Code]
          | PUT | GET | PUTI Int | GETI Int
          | PUSH Int | POP | DUP | SWAP | EXCH
          | INC | DEC | NEG
          | ADD | MUL | SUB | DIV | MOD
          | EQL | LTH | GTH | NEQ
          | ASK | PRT | PRTS String
          | FORK [Code] [Code]
          deriving (Read, Show, Eq)

newtype ActionM m a = ActionM {runActionM :: a -> m a}

instance Monad m => Semigroup (ActionM m a) where
  ActionM f <> ActionM g = ActionM (f >=> g)

instance Monad m => Monoid (ActionM m a) where
  ActionM f `mappend` ActionM g = ActionM (f >=> g)
  mempty = ActionM return

newtype Program m a = Program { getProgram :: ([Code], ActionM m (VM a)) }
  deriving (Semigroup, Monoid)

type Program' m a = (Code -> VM a -> m (VM a)) -> Program m a
type Pure a = Program' Identity a

program c f p = Program . ([c],) . ActionM $
  \vm -> p c =<< f (stack vm) vm
  -- \vm -> case status vm of
  --   Nothing -> p c =<< f (stack vm) vm
  --   m -> return vm

programM c f p = Program . ([c],) . ActionM $
  \vm -> p c =<< f (memory vm, stack vm) vm
  -- \vm -> case status vm of
  --   Nothing -> p c =<< f (memory vm, stack vm) vm
  --   m -> return vm

run :: Monad m => Program m a -> VM a -> m (VM a) 
run = runActionM . snd . getProgram

toCode :: Monad m => Program' m a -> [Code]
toCode prog = fst . getProgram $ prog none

none :: Monad m => Code -> VM a -> m (VM a)
none = const return

-- запуск программы вне монад
exec :: Pure () -> VM ()
exec = runIdentity . execM

execM :: Monad m => Program' m () -> m (VM ())
execM prog = run (prog none) (mkVM ())

execLog p prog = run (prog logger) (mkVM mempty)
  where logger c vm = return $ addRecord (p c vm) vm

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

debug p = unlines . reverse . journal <$> execLog logRun p

------------------------------------------------------------
pop,dup,swap,exch,put,get :: Monad m => Program' m a
puti,geti,push :: Monad m => Int -> Program' m a
add,mul,sub,frac,modulo,inc,dec,neg :: Monad m => Program' m a
eq,neq,lt,gt :: Monad m => Program' m a

err m = setStatus . Just $ "Error : " ++ m

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

puti i = indexed (PUTI i) i $
    \case (m, x:s) -> setStack s <=< setMemory (m // [(i,x)])
          _ -> err "put expected an argument"

geti i = indexed (GETI i) i $ \(m, s) -> setStack ((m ! i) : s)

put = programM PUT $ 
    \case (m, i:x:s) -> setStack s <=< setMemory (m // [(i,x)])
          _ -> err "put expected an argument"

get = programM GET $ \(m, i:s) -> setStack ((m ! i) : s)


indexed c i f = programM c $ if (i < 0 || i >= memSize)
                             then const $ err "index in [0,16]"
                             else f

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

proceed p prog s = run (prog p) <=< setStack s

rep body p = program (REP (toCode body)) go none
  where go (n:s) = if n >= 0
                   then proceed p (stimes n body) s
                   else err "rep expected positive argument."
        go _ = err "rep expected an argument."

branch br1 br2 p = program (IF (toCode br1) (toCode br2)) go none
   where go (x:s) = proceed p (if (x /= 0) then br1 else br2) s
         go _ = err "branch expected an argument."

while test body p = program (WHILE (toCode test) (toCode body)) (const go) none
  where go vm = do res <- proceed p test (stack vm) vm
                   case (stack res) of
                     0:s -> proceed p mempty s res
                     _:s -> go =<< proceed p body s res
                     _ -> err "while expected an argument." vm

ask :: Program' IO a
ask = program ASK $
  \case s -> \vm -> do x <- getLine
                       setStack (read x:s) vm

prt :: Program' IO a
prt = program PRT $
  \case x:s -> \vm -> print x >> return vm
        _ -> err "PRT expected an argument"

prtS :: String -> Program' IO a
prtS s = program (PRTS s) $
  const $ \vm -> print s >> return vm

fork :: Program' [] a -> Program' [] a -> Program' [] a
fork br1 br2 p = program (FORK (toCode br1) (toCode br2)) (const go) none
  where go = run (br1 p) <> run (br2 p)

------------------------------------------------------------

fromCode :: Monad m => [Code] -> Program' m a
fromCode = hom
  where
    hom = foldMap $ \case
      IF b1 b2 -> branch (hom b1) (hom b2)
      REP p -> rep (hom p)
      WHILE t b -> while (hom t) (hom b)
      PUTI i -> puti i
      GETI i -> geti i
      PUT -> put
      GET -> get
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
      _ -> mempty

fromCodeIO :: [Code] -> Program' IO a
fromCodeIO = hom
  where
    hom = foldMap $ \case
      IF b1 b2 -> branch (hom b1) (hom b2)
      REP p -> rep (hom p)
      WHILE t b -> while (hom t) (hom b)
      ASK -> ask
      PRT -> ask
      PRTS s -> prtS s
      c -> fromCode [c]

fromCodeList :: [Code] -> Program' [] a
fromCodeList = hom
  where
    hom = foldMap $ \case
      IF b1 b2 -> branch (hom b1) (hom b2)
      REP p -> rep (hom p)
      WHILE t b -> while (hom t) (hom b)
      FORK b1 b2 -> fork (hom b1) (hom b2)
      c -> fromCode [c]

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

arity :: Monad m => Program' m a -> Arity
arity = arity' . toCode

arity' :: [Code] -> Arity
arity' = hom
  where
    hom = foldMap $
      \case
        IF b1 b2 -> let i1:>o1 = hom b1
                        i2:>o2 = hom b2
                    in 1:>0 <> i1 `max` i2 :> o1 `min` o2
        REP p -> 1:>0
        WHILE t b -> hom t <> 1:>0
        FORK b1 b2 -> hom $ [IF b1 b2]
        PUTI _ -> 1:>0
        GETI _ -> 0:>1
        PUT -> 2:>0
        GET -> 1:>1
        PUSH _ -> 0:>1
        POP -> 1:>0
        DUP -> 1:>2
        SWAP -> 2:>2
        EXCH -> 2:>3
        INC -> 1:>1
        DEC -> 1:>1
        NEG -> 1:>1
        _   -> 2:>1

------------------------------------------------------------
-- pretty printing as a homomorpism: Program -> String

listing :: Monad m => Program' m a -> String
listing = unlines . printCode 0 . toCode
  where
    printCode n = foldMap f
      where
        f = \case
          IF b1 b2 -> print "IF" <> indent b1 <> print ":" <> indent b2
          REP p -> print "REP" <> indent p
          WHILE t b -> print "WHILE" <> indent t <> indent b
          FORK b1 b2 -> print "FORK" <> indent b1 <>
                        print " /" <> print " \\" <> indent b2
          c -> print $ show c

        print x = [stimes n "  " ++ x]
        indent = printCode (n+1)

------------------------------------------------------------
-- memory requirements as a homomorpism: Program -> Max Int

memoryUse :: Monad m => Program' m a -> Max Int
memoryUse = memoryUse' . toCode

memoryUse' = hom
  where
    hom = foldMap $
      \case
        IF b1 b2 -> hom b1 <> hom b2
        REP p -> hom p
        WHILE t b -> hom t <> hom b
        FORK t b -> hom t <> hom b
        PUTI i -> Max (i+1)
        GETI i -> Max (i+1)
        _ -> 0

------------------------------------------------------------
-- reduction using homomorphisms : `arity` and `memoryUse`
-- works only for pure code

isReducible :: [Code] -> Bool
isReducible p = case arity' p of
                  0:>_ -> memoryUse' p == 0
                  _    -> False

reducible :: [Code] -> [[Code]]
reducible = go []
  where go res [] = reverse res
        go res (p:ps) = if isReducible [p]
                        then let (a,b) = spanBy isReducible (p:ps)
                             in go (a:res) b
                        else go res ps

spanBy test l = case foldMap tst $ zip (inits l) (tails l) of
                  Last Nothing -> ([],l)
                  Last (Just x) -> x
  where tst x = Last $ if test (fst x) then Just x else Nothing 


reduce :: Pure a -> Pure a
reduce = fromCode . reduce' . toCode

reduce' :: [Code] -> [Code]
reduce' p = process (reducible p) p
  where
    process = appEndo . foldMap (\x -> Endo $ x `replaceBy` shrink x)
    shrink = foldMap (\x -> [PUSH x]) . reverse . stack . exec . fromCode
    replaceBy x y = intercalate y . splitOn x


------------------------------------------------------------
-- Example programs

fact,range,fact1,fact2,fact3,copy2,gcd1,pow :: Monad m => Program' m a

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

fact3 = dup <> puti 0 <> dup <> dec <>
        rep
        (
          dec <> dup <> geti 0 <> mul <> puti 0
        ) <>
        geti 0 <> swap <> pop

copy2 = exch <> exch

gcd1 = while (copy2 <> neq)
       (
         copy2 <> lt <> branch mempty swap <> exch <> sub
       ) <>
       pop

pow = swap <> puti 0 <> push 1 <> puti 1 <>
      while (dup <> push 0 <> gt)
      (
        dup <> push 2 <> modulo <>
        branch (dec <> geti 0 <> dup <> geti 1 <> mul <> puti 1) (geti 0) <>
        dup <> mul <> puti 0 <>
        push 2 <> frac
      ) <>
      pop <> geti 1

ioprog :: Program' IO a
ioprog = prtS "first number" <> ask
         <> prtS "second number" <> ask
         <> rep (prt <> dup <> inc)
         <> prt

test :: Monad m => Program' m a 
test = push 8 <>
  dup <> fact1 <> swap <>
  dup <> fact2 <> swap <>
  dup <> fact3 <> swap <>
  push 54 <> gcd1 <>
  dup <> push 20 <> pow 


fillMemory :: Monad m => Program' m a
fillMemory = dup <> dup <> puti 0 <> 
             while (dup <> push memSize <> geti 0 <> sub <> lt)
             (
               exch <> add <> dup <> push 1 <> swap <> put
             ) <>
             pop <> pop

fill :: Program' IO a
fill = dup <> dup <> puti 0 <>
       while (dup <> push memSize <> geti 0 <> sub <> lt)
       (geti 0 <> add <> dup <> push 1 <> swap <> put) <>
       pop

sieve :: Program' IO a
sieve = push 2 <>
        while (dup <> dup <> mul <> push memSize <> lt)
        (dup <> get <> branch mempty fill <> inc)

main = execM (sieve <> prtS "Ok")

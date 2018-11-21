{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, TupleSections, BangPatterns #-}

module Main where

import Data.Monoid hiding ((<>))
import Data.Semigroup (Semigroup(..),stimes,Max(..))
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.Identity
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as M

type Stack = [Int]

memSize = 65536 --36

data VM a = VM { stack :: Stack
               , status :: Maybe String
               , journal :: a }
            deriving Show

mkVM = VM mempty mempty

{-# INLINE setStack #-} 
setStack  x (VM _ st l) = return $ VM x st l
setStatus st (VM s _ l) = return $ VM s st l
addRecord x (VM s st l) = return $ VM s st (x l)

------------------------------------------------------------

data Code = IF [Code] [Code]
          | REP [Code]
          | WHILE [Code] [Code]
          | PUTI Int | GETI Int | PUT | GET
          | PUSH Int | POP | DUP | SWAP | EXCH
          | INC | DEC | NEG
          | ADD | MUL | SUB | DIV | MOD
          | EQL | LTH | GTH | NEQ
          | ASK | PRT | PRTS String
          | FORK [Code] [Code]
          deriving (Read, Show, Eq)

------------------------------------------------------------

newtype ActionM m a = ActionM {runActionM :: a -> m a}

instance Monad m => Semigroup (ActionM m a) where
  ActionM f <> ActionM g = ActionM (f >=> g)

instance Monad m => Monoid (ActionM m a) where
  ActionM f `mappend` ActionM g = ActionM (f >=> g)
  mempty = ActionM return

------------------------------------------------------------

newtype Program m a = Program { getProgram :: ([Code], ActionM m (VM a)) }
  deriving (Semigroup, Monoid)

type Memory m = M.MVector (PrimState m) Int
type Logger m a = Maybe (Memory m  -> Code -> VM a -> m (VM a))
type Program' m a = Logger m a -> Memory m -> Program m a

programM c f l v = Program . ([c],) . ActionM $
  \vm -> case status vm of
    Nothing -> go vm
    _ -> return vm
  where
    go = case l of
      Just p -> \vm -> p v c =<< f v (stack vm) vm
      _ -> \vm -> f v (stack vm) vm

program c f = programM c (const f)

run :: Monad m => Program m a -> VM a -> m (VM a) 
run = runActionM . snd . getProgram

toCode :: Monad m => Program' m a -> [Code]
toCode prog = fst . getProgram $ prog Nothing undefined

exec :: Program' Identity () -> VM ()
exec prog = runIdentity $ run (prog Nothing undefined) (mkVM ())

execM :: PrimMonad m => Program' m () -> m (VM ())
execM prog = do m <- M.replicate memSize 0
                run (prog Nothing m) (mkVM ())

execList :: Program' [] () -> [VM ()]
execList prog = run (prog Nothing undefined) (mkVM ())

--execLogM :: (Semigroup a, Monoid a, PrimMonad m) => (Code -> VM a -> a) -> Program' m a -> m (VM a)
execLogM p prog = do m <- M.replicate memSize 0
                     run (prog (Just logger) m) (mkVM mempty)
  where logger m c vm = do m' <- V.freeze m
                           addRecord (p m' c vm <>) vm

execLog p x0 prog = do m <- M.replicate memSize 0
                       run (prog (Just logger) m) (mkVM x0)
  where logger m c = addRecord (p undefined c)
                           

f &&& g = \c -> \r -> (f c r, g c r)

logStack _ _ vm   = [stack vm]
logStackUsed _ _ = Max . length . stack
logSteps _ _ !x = x + 1
logSteps' _ _ _ = Sum 1
logCode _ c _   = [c]
logRun mem com vm = [pad 10 c ++ "| " ++ pad 20 s ++ "| " ++ m ]
  where c = show com
        m = unwords $ show <$> V.toList mem
        s = unwords $ show <$> stack vm
        pad n x = take n (x ++ repeat ' ')

debug :: Program' IO [String] -> IO ()
debug p = do res <- execLogM logRun p
             putStrLn (unlines . reverse . journal $ res) 

------------------------------------------------------------
pop,dup,swap,exch :: Monad m => Program' m a
push :: Monad m => Int -> Program' m a
add,mul,sub,frac,modulo,inc,dec,neg :: Monad m => Program' m a
eq,neq,lt,gt :: Monad m => Program' m a

err m = setStatus . Just $ "Error : " ++ m

{-# INLINE pop #-}
pop = program POP $ 
  \case (_:s) -> setStack s
        _ -> err "pop expected an argument."

{-# INLINE push #-}
push x = program (PUSH x) $ \s -> setStack (x:s)

{-# INLINE dup #-}
dup = program DUP $ 
  \case (x:s) -> setStack (x:x:s)
        _ -> err "dup expected an argument."

{-# INLINE swap #-}
swap = program SWAP $ 
  \case (x:y:s) -> setStack (y:x:s)
        _ -> err "swap expected two arguments."

{-# INLINE exch #-}
exch = program EXCH $ 
  \case (x:y:s) -> setStack (y:x:y:s)
        _ -> err "expected two arguments."

{-# INLINE unary #-}
unary c f = program c $
  \case (x:s) -> setStack (f x:s)
        _ -> err $ "operation " ++ show c ++ " expected an argument"

{-# INLINE binary #-}
binary c f = program c $
  \case (x:y:s) -> setStack (f x y:s)
        _ -> err $ "operation " ++ show c ++ " expected two arguments"

{-# INLINE add #-}
add = binary ADD (+)
{-# INLINE sub #-}
sub = binary SUB (flip (-))
{-# INLINE mul #-}
mul = binary MUL (*)
{-# INLINE frac #-}
frac = binary DIV (flip div)
{-# INLINE modulo #-}
modulo = binary MOD (flip mod)
{-# INLINE neg #-}
neg = unary NEG (\x -> -x)
{-# INLINE inc #-}
inc = unary INC (\x -> x+1)
{-# INLINE dec #-}
dec = unary DEC (\x -> x-1)
{-# INLINE eq #-}
eq = binary EQL (\x -> \y -> if (x == y) then 1 else 0)
{-# INLINE neq #-}
neq = binary NEQ (\x -> \y -> if (x /= y) then 1 else 0)
{-# INLINE lt #-}
lt = binary LTH (\x -> \y -> if (x > y) then 1 else 0)
{-# INLINE gt #-}
gt = binary GTH (\x -> \y -> if (x < y) then 1 else 0)

{-# INLINE proceed #-}
proceed m p prog s = run (prog p m) <=< setStack s

rep body p m = program (REP (toCode body)) go Nothing m
  where go (n:s) = if n >= 0
                   then proceed m p (stimes n body) s
                   else err "rep expected positive argument."
        go _ = err "rep expected an argument."

branch br1 br2 p m = program (IF (toCode br1) (toCode br2)) go Nothing m
   where go (x:s) = proceed m p (if (x /= 0) then br1 else br2) s
         go _ = err "branch expected an argument."

while test body p m = program (WHILE (toCode test) (toCode body)) (const go) Nothing m
  where go vm = do res <- proceed m p test (stack vm) vm
                   case (stack res) of
                     (0:s) -> proceed m p mempty s res
                     _:s -> go =<< proceed m p body s res
                     _ -> err "while expected an argument." vm

ask :: Program' IO a
ask = program ASK $
  \case s -> \vm -> do x <- getLine
                       setStack (read x:s) vm

prt :: Program' IO a
prt = program PRT $
  \case (x:s) -> \vm -> print x >> return vm
        _ -> err "PRT expected an argument"

prtS :: String -> Program' IO a
prtS s = program (PRTS s) $
  const $ \vm -> print s >> return vm

fork :: Program' [] a -> Program' [] a -> Program' [] a
fork br1 br2 p m = program (FORK (toCode br1) (toCode br2)) (const go) Nothing m
  where go = run (br1 p m) <> run (br2 p m)

geti :: PrimMonad m => Int -> Program' m a
{-# INLINE geti #-}
geti i = programM (GETI i) $
  \m -> \s -> \vm -> do x <- M.unsafeRead m i
                        setStack (x:s) vm

puti :: PrimMonad m => Int -> Program' m a
{-# INLINE puti #-}
puti i = programM (PUTI i) $
  \m -> \case (x:s) -> \vm -> M.unsafeWrite m i x >> setStack s vm
              _ -> err "expected an element"

get :: PrimMonad m => Program' m a
{-# INLINE get #-}
get = programM (GET) $
  \m -> \case (i:s) -> \vm -> do x <- M.read m i
                                 setStack (x:s) vm
              _ -> err "expected an element"

put :: PrimMonad m => Program' m a
{-# INLINE put #-}
put = programM (PUT) $
  \m -> \case (i:x:s) -> \vm -> M.write m i x >> setStack s vm
              _ -> err "expected two elemets"

------------------------------------------------------------

fromCode :: Monad m => [Code] -> Program' m a
fromCode = hom
  where
    hom = foldMap $ \case
      IF b1 b2 -> branch (hom b1) (hom b2)
      REP p -> rep (hom p)
      WHILE t b -> while (hom t) (hom b)
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

fromCodeM ::  PrimMonad m => [Code] -> Program' m a
fromCodeM = hom
  where
    hom = foldMap $ \case
      IF b1 b2 -> branch (hom b1) (hom b2)
      REP p -> rep (hom p)
      WHILE t b -> while (hom t) (hom b)
      PUTI i -> puti i
      GETI i -> geti i
      PUT -> put
      GET -> get
      c -> fromCode [c]

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
          IF b1 b2 -> output "IF" <> indent b1 <> output ":" <> indent b2
          REP p -> output "REP" <> indent p
          WHILE t b -> output "WHILE" <> indent t <> indent b
          FORK b1 b2 -> output "FORK" <> indent b1 <>
                        output " /" <> output " \\" <> indent b2
          c -> output $ show c

        output x = [stimes n "  " ++ x]
        indent = printCode (n+1)


------------------------------------------------------------
-- Example programs

fact,range,fact1,fact2,copy2,gcd1 :: Monad m => Program' m a

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

copy2 = exch <> exch

gcd1 = while (copy2 <> neq)
       (
         copy2 <> lt <> branch mempty swap <> exch <> sub
       ) <>
       pop

fact3,pow :: PrimMonad m => Program' m a
fact3 = dup <> puti 0 <> dup <> dec <>
        rep
        (
          dec <> dup <> geti 0 <> mul <> puti 0
        ) <>
        geti 0 <> swap <> pop

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

test :: Program' IO a 
test = stimes 100 $
  push 8 <>
  dup <> fact1 <> swap <>
  dup <> fact2 <> swap <>
  dup <> fact3 <> swap <>
  push 54 <> gcd1 <> pow <> gcd1 <> eq <> pop

fill :: Program' IO a
fill = dup <> dup <> puti 0 <>
       while (dup <> push memSize <> geti 0 <> sub <> lt)
       (geti 0 <> add <> push 1 <> exch <> put) <>
       pop

sieve :: Program' IO a
sieve = push 2 <>
        while (dup <> dup <> mul <> push memSize <> lt)
        (dup <> get <> branch mempty fill <> inc) 

main = print =<< journal <$> execLog logSteps 0 (stimes 100 sieve <> prtS "Ok")
-- main = execM (stimes 100 sieve <> prtS "Ok")

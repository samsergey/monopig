{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, TupleSections #-}

module Main where

import Data.Monoid hiding ((<>))
import Data.Semigroup (Semigroup(..),stimes,Max(..))
import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Control.Monad.Identity
import Control.DeepSeq
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as M

type Stack = [Int]

memSize :: Int
memSize = 65536

data VM a = VM { stack :: !Stack
               , status :: Maybe String
               , journal :: !a }
            deriving Show

mkVM = VM mempty mempty

{-# INLINE setStack #-} 
setStack  x (VM _ st l) = return $ VM x st l
setStatus st (VM s _ l) = return $ VM s st l
{-# INLINE addRecord #-} 
addRecord x (VM s st l) = return $ VM s st (x <> l)

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
  mappend = (<>)
  mempty = ActionM return

------------------------------------------------------------

newtype Program m a = Program { getProgram :: ([Code], ActionM m (VM a)) }
  deriving (Semigroup, Monoid)

type Memory m = M.MVector (PrimState m) Int
type Logger m a = Maybe (Memory m  -> Code -> VM a -> m (VM a))
type Program' m a = Logger m a -> Memory m -> Program m a

program code f = programM code (const f)

programM code f (Just logger) mem = Program . ([code],) . ActionM $
  \vm -> case status vm of
    Nothing -> logger mem code =<< f mem (stack vm) vm
    _ -> return vm
programM code f _ mem = Program . ([code],) . ActionM $
  \vm -> case status vm of
    Nothing -> f mem (stack vm) vm
    _ -> return vm

run :: Monad m => Program m a -> VM a -> m (VM a) 
run = runActionM . snd . getProgram

toCode :: Monad m => Program' m a -> [Code]
toCode prog = fst . getProgram $ prog Nothing undefined

exec :: Program' Identity () -> VM ()
exec prog = runIdentity $ run (prog Nothing undefined) (mkVM ())

execM :: PrimMonad m => Program' m () -> m (VM ())
execM prog = do mem <- M.replicate memSize 0
                run (prog Nothing mem) (mkVM ())

execList :: Program' [] () -> [VM ()]
execList prog = run (prog Nothing undefined) (mkVM ())

--execLogM :: (Semigroup a, Monoid a, PrimMonad m) => (Code -> VM a -> a) -> Program' m a -> m (VM a)
execLogM logger prog = do mem <- M.replicate memSize 0
                          run (prog (Just l) mem) (mkVM mempty)
  where l mem code vm = do mem' <- V.freeze mem
                           addRecord (logger mem' code vm) vm

--
execLog :: (PrimMonad m,  Semigroup a, Monoid a, NFData a) => (Memory m  -> Code -> VM a -> a) -> Program' m a -> m (VM a)
execLog logger prog = do mem <- M.replicate memSize 0
                         run (prog (Just l) mem) (mkVM mempty)
  where l _ code vm = logger undefined code vm `deepseq` addRecord (logger undefined code vm) vm


f &&& g = \m -> \c -> \r -> (f m c r, g m c r)

logStack _ _ vm   = [stack vm]
logStackUsed _ _ = Max . length . stack
logSteps _ _ _ = Sum (1 :: Int)
logCode _ code _   = [code]
logRun mem code vm = [pad 10 c ++ "| " ++ pad 20 s ++ "| " ++ m ]
  where c = show code
        m = unwords $ show <$> V.toList mem
        s = unwords $ show <$> stack vm
        pad n x = take n (x ++ repeat ' ')

debug :: Program' IO [String] -> IO ()
debug prog = do res <- execLogM logRun prog
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
  \case s@(x:_) -> setStack (x:s)
        _ -> err "dup expected an argument."

{-# INLINE swap #-}
swap = program SWAP $ 
  \case (x:y:s) -> setStack (y:x:s)
        _ -> err "swap expected two arguments."

{-# INLINE exch #-}
exch = program EXCH $ 
  \case s@(_:y:_) -> setStack (y:s)
        _ -> err "expected two arguments."

{-# INLINE unary #-}
unary code f = program code $
  \case (x:s) -> setStack (f x:s)
        _ -> err $ "operation " ++ show code ++ " expected an argument"

{-# INLINE binary #-}
binary code f = program code $
  \case (x:y:s) -> setStack (f x y:s)
        _ -> err $ "operation " ++ show code ++ " expected two arguments"

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
proceed prog s logger mem = setStack s >=> run (prog logger mem)

rep body logger mem = program code f Nothing mem
  where
    code = REP (toCode body)
    f (n:s) = if n >= 0
               then proceed (stimes n body) s logger mem
               else err "REP expected positive argument."
    f _ = err "REP expected an argument."

branch br1 br2 logger mem = program code f Nothing mem
   where
     code = IF (toCode br1) (toCode br2)
     f (x:s) = proceed (if (x == 0) then br2 else br1) s logger mem
     f _ = err "BRANCH expected an argument."

while test body logger mem = program code f Nothing mem
  where
    code = WHILE (toCode test) (toCode body)
    f _ = run (test logger mem) >=> f'
    f' vm =
      case stack vm of
        0:s -> setStack s vm
        _:s -> proceed (body <> test) s logger mem vm >>= f'
        _ -> err "WHILE expected an argument." vm

ask :: Program' IO a
ask = program ASK $
  \case s -> \vm -> do x <- getLine
                       setStack (read x:s) vm

prt :: Program' IO a
prt = program PRT $
  \case (x:_) -> \vm -> print x >> return vm
        _ -> err "PRT expected an argument"

prtS :: String -> Program' IO a
prtS s = program (PRTS s) $
  const $ \vm -> print s >> return vm


fork :: Program' [] a -> Program' [] a -> Program' [] a
fork br1 br2 logger mem = program (FORK (toCode br1) (toCode br2)) (const go) Nothing mem
  where go = run (br1 logger mem) <> run (br2 logger mem)

geti :: PrimMonad m => Int -> Program' m a
{-# INLINE geti #-}
geti i = programM (GETI i) $
  \mem -> \s -> if (0 <= i && i < memSize)
                then \vm -> do x <- M.unsafeRead mem i
                               setStack (x:s) vm
                else err "GETI got index out of range"

puti :: PrimMonad m => Int -> Program' m a
{-# INLINE puti #-}
puti i = programM (PUTI i) $
  \mem -> \case (x:s) -> if (0 <= i && i < memSize)
                         then \vm -> M.unsafeWrite mem i x >> setStack s vm
                         else err "PUTI got index out of range"
                _ -> err "PUTI expected an element"

get :: PrimMonad m => Program' m a
{-# INLINE get #-}
get = programM (GET) $
  \mem -> \case (i:s) -> \vm -> do x <- M.read mem i
                                   setStack (x:s) vm
                _ -> err "GET expected an element"

put :: PrimMonad m => Program' m a
{-# INLINE put #-}
put = programM (PUT) $
  \mem -> \case (i:x:s) -> \vm -> M.write mem i x >> setStack s vm
                _ -> err "PUT expected two elemets"

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

fill :: PrimMonad m => Program' m a
fill = dup <> dup <> add <>
       while (dup <> push memSize <> lt)
       (dup <> push 1 <> swap <> put <> exch <> add) <>
       pop

sieve :: PrimMonad m => Program' m a
sieve = push 2 <>
        while (dup <> dup <> mul <> push memSize <> lt)
        (dup <> get <> branch mempty fill <> inc) <>
        pop

--main = print =<< journal <$> execLog (logSteps &&& logStackUsed) (stimes 10 sieve <> prtS "Ok")
--main = execM (stimes 100 sieve <> prtS "Ok")

fill' :: Int -> Int -> Memory IO -> IO (Memory IO)
fill' k n m
  | n > memSize-k = return m
  | otherwise = M.unsafeWrite m n 1 >> fill' k (n+k) m

sieve' :: Int -> Memory IO -> IO (Memory IO)
sieve' k m
  | k*k < memSize =
      do x <- M.unsafeRead m k
         if x == 0
           then fill' k (2*k) m >>= sieve' (k+1)
           else sieve' (k+1) m
  | otherwise = return m
  
mtimes n = mconcat . replicate n

main = do m <- M.replicate memSize 0
          mtimes 100 (sieve' 2 m >> return ())
          print "Ok" 


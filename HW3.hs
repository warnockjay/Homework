{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
module HW3 where

import Text.Read (readMaybe)
import Text.Parsec

-- * Question 1: Applicative Trees

data Tree a = T a [Tree a]
  deriving (Eq,Ord,Show)

instance Functor Tree where
  fmap :: (a -> b) -> Tree a -> Tree b
  fmap f (T x []) = T (f x) []
  fmap f (T x ts)  = T (f x) (map (fmap f) ts)

instance Applicative Tree where
  pure :: a -> Tree a
  pure x = T x []
  (<*>) :: Tree (a -> b) -> Tree a -> Tree b
  (<*>) (T f []) (T x []) = T (f x) []
  (<*>) (T f []) (T x l)  = T (f x) (map (fmap f) l)
  (<*>) (T f fts) (T x []) = T (f x) [functree <*> T x [] | functree <- fts]
  (<*>) (T f fts) (T x ts)  = T (f x) (map (fmap f) ts ++ [functree <*> T x ts | functree <- fts])


{-

(i)
Claim: fmap id == id
That is, for any (t :: Tree a) we want to show that fmap id t == id t.
Proof:
Take any t = T x ts.
As induction hypothesis, assume we have
  fmap id t1 == id t1
for any t1 in ts.
Then we have:

fmap id (T x ts)
==                                
T ...
==                                (put your justification here)
...
==
id (T x ts)

(ii)
Claim: fmap (f . g) == fmap f . fmap g
Proof:
...

(iii)
Claim: fmap f == (pure f <*>)
Proof:
...

(iv)
Claim: pure id <*> == id
Proof:
...

(v)
Claim: pure (.) <*> f <*> g <*> x == f <*> (g <*> x)
Proof:
...

(vi)
Claim: pure f <*> pure x == pure (f x)
Proof:
...

(vii)
Claim: u <*> pure y == pure ($ y) <*> u
Proof:
...

-}

treeEqUpto :: Eq a => Int -> Tree a -> Tree a -> Bool
treeEqUpto 0 _         _         = True
treeEqUpto k (T x xts) (T y yts) = x == y && and (take k $ zipWith (treeEqUpto (k-1)) xts yts)

-- * Question 2: Applicatives as lax monoidal functors

phi :: forall f a b . Applicative f => (f a, f b) -> f (a , b)
phi = up . right . down where
  down (f, g)  = (fmap (,) f, g) 
  right (f, g) = ((f <*>), g)
  up (f, g)    = f g

-- * Question 3: Parsing Logical Formulas

data Form = P Integer | Neg Form | Dia Form | Conj Form Form | Imp Form Form
  deriving (Eq,Show)

pForm :: Parsec String () Form
pForm = pImp

pImp :: Parsec String () Form
pImp = chainr1 pConj (try (spaces >> string "->" >> spaces >> return Imp))

pConj :: Parsec String () Form
pConj = chainl1 pUnary (try (spaces >> char '&' >> spaces >> return Conj))

pUnary :: Parsec String () Form
pUnary = try pNeg <|> try pDia <|> pAtom
  where
    pNeg = char '!' >> spaces >> (Neg <$> pUnary)
    pDia = string "<>" >> spaces >> (Dia <$> pUnary)

pAtom :: Parsec String () Form
pAtom = pVar <|> (char '(' >> spaces >> pImp <* spaces <* char ')')
  where
    pVar = char 'p' >> (P . read <$> many1 digit)


parseForm :: String -> Either ParseError Form
parseForm = parse pForm "input"

-- * Question 4: Hello World 3.

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing  = False

dialogue :: IO ()
dialogue = do
  putStrLn "Hello! Who are you?"
  name <- getLine
  putStrLn $ "Nice to meet you, " ++ name ++ "!"
  putStrLn "How old are you?"
  age <- getLine
  if isJust (readMaybe age :: Maybe Int)
    then putStrLn $ "Ah so you were born in " ++ show (2024- read age) ++ " or " ++ show (2025 - read age)
  else
    putStrLn "Sorry, that is not a number" 

-- * Question 5: StateIO

newtype StateIO  s a = SIO {runSIO :: s -> IO (a, s)}  -- for parts (a) to (c)
newtype StateT m s a = ST  {run    :: s -> m  (a, s)}  -- for part (d)

instance Monad m => Functor (StateT m s) where
  fmap f (ST sa) = ST $ \s -> do
    (a, s') <- sa s
    return (f a, s') 
instance Monad m => Applicative (StateT m s) where
  pure a = ST $ \s -> return (a, s)
  (ST sf) <*> (ST sa) = ST $ \s -> do
    (f, s')  <- sf s
    (a, s'') <- sa s'
    return (f a, s'') 

put :: s -> StateIO s ()
put s' = SIO $ \_s -> return ((), s')

get :: StateIO s s
get = SIO $ \s -> return (s, s)


lift :: Monad m => m a -> StateT m s a
lift ma = ST $ \s -> do
  a <- ma
  return (a, s)

instance Functor (StateIO s) where
  fmap :: (a -> b) -> StateIO s a -> StateIO s b
  fmap ab (SIO sa) = SIO $ \s -> do
    (a, s') <- sa s
    let b = ab a
    return (b, s')

instance Applicative (StateIO s) where
  pure a = SIO $ \s -> return (a, s)
  (SIO sab) <*> (SIO sa) = SIO $ \s -> do
    (ab, s' ) <- sab s
    (a , s'') <- sa  s'
    let b = ab a
    return (b, s'')

instance Monad m => Monad (StateT m s) where
  (ST sa) >>= f = ST $ \s -> do
    (a, s') <- sa s
    run (f a) s'

putT :: Monad m => s -> StateT m s ()
putT s' = ST $ \_ -> return ((), s')

getT :: Monad m => StateT m s s
getT = ST $ \s -> return (s, s)

askCount :: StateT IO Int ()
askCount = do
  lift $ putStrLn "What is your name?"
  n <- lift getLine
  lift $ putStrLn $ "Nice to meet you, " ++ n ++ "."
  k <- getT
  let k' = k + length (filter (`elem` "aeiou") n)
  putT k'
  lift $ putStrLn $ "I have seen " ++ show k' ++ " vowels so far."
  askCount

safeLogDivide :: String -- remove this line after you are done with (d) --
safeLogDivide = undefined -- remove this line after you are done with (d) --
{- -- remove this line after you are done with (d) --
-- monad m=Maybe, state type s=[String], value type a=Int
safeLogDivide :: Int -> Int -> StateT Maybe [String] Int
safeLogDivide _ 0 = lift Nothing
safeLogDivide x y = do
  oldLog <- get
  put $ oldLog ++ ["Divided by " ++ show y]
  return (x `div` y)
-} -- remove this line after you are done with (d) --

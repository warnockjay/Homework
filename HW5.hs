module HW5 where

import Data.List()
import Data.Maybe
import Control.Arrow (Arrow(second))

-- * Question 1: PAL

(!) :: Eq a => [(a,b)] -> a -> b
(!) v x = fromJust (lookup x v)

(?) :: Eq a => [[a]] -> a -> [a]
(?) lls x = head (filter (x `elem`) lls)

type Prop = Int
type Agent = String

data Form = Top | P Prop | Neg Form | Con Form Form | K Agent Form | Ann Form Form
  deriving (Eq,Ord,Show)

type World = Int
type Relations = [(Agent, [[World]])]
type Valuation = [(World, [Prop])]
data Model = Mo { worlds :: [World]
                , rel :: Relations
                , val :: Valuation }
  deriving (Eq,Ord,Show)

isTrue :: (Model,World) -> Form -> Bool
isTrue _     Top       = True
isTrue (m,w) (P p)     = p `elem` (val m ! w)
isTrue (m,w) (Neg f)   = not (isTrue (m,w) f)
isTrue (m,w) (Con f g) = isTrue (m,w) f && isTrue (m,w) g
isTrue (m,w) (K i f)   = and [ isTrue (m,w') f | w' <- (rel m ! i) ? w ]
isTrue (m,w) (Ann f g) = isTrue (m,w) f <= isTrue (announce m f, w) g

(|=) :: (Model,World) -> Form -> Bool
(|=) = isTrue

announce :: Model -> Form -> Model
announce oldModel f = Mo newWorlds newRel newVal where
  newWorlds = [w | w <- worlds oldModel, (oldModel,w) |= f]
  newRel    = [ second (map (filter (\ y -> (oldModel, y) |= f))) x | x <- rel oldModel]
  newVal    = filter (\x -> (oldModel,fst x) |= f) (val oldModel)

kw :: Agent -> Form -> Form
kw i f = dis (K i f) (K i (Neg f))

muddyStart :: Model
muddyStart = Mo
  [0,1,2,3,4,5,6,7]
  [("1",[[0,4],[2,6],[3,7],[1,5]])
  ,("2",[[0,2],[4,6],[5,7],[1,3]])
  ,("3",[[0,1],[4,5],[6,7],[2,3]])]
  [(0,[]) ,(1,[3])  ,(2,[2])  ,(3,[2,3])
  ,(4,[1]),(5,[1,3]),(6,[1,2]),(7,[1,2,3])]

dis :: Form -> Form -> Form
dis f g = Neg (Con (Neg f) (Neg g))

atLeastOne :: Form
atLeastOne = dis (P 1) (dis (P 2) (P 3))

conSet :: [Form] -> Form
conSet = foldr Con Top

nobodyKnowsOwn :: Form
nobodyKnowsOwn = conSet [Neg (kw (fst n) (P $ read $ fst n)) | n <- rel muddyStart]

everyoneKnowsAll :: Form
everyoneKnowsAll = conSet [conSet [kw (fst n) (P $ read $ fst m) | m <- rel muddyStart] | n <- rel muddyStart]

-- * Question 2: NSA Puzzle: Explicit Solution

data Class = Calc1 | Calc2 | Calc3 deriving (Eq,Ord,Show,Enum)
type Time = Int -- should only be 3, 9, 10, 11 or 12
data Building = North | East | South | West deriving (Eq,Ord,Show,Enum)
type Case = (Class, Time, Building)

-- Use the following atomic propositions:
-- 1,2,3, -- Calc1, Calc2, Calc3
-- 103,109,110,111,112 -- 3, 9, 10, 11, 12/noon
-- 201,202,203,204 -- North, East, South, West

julia, michael, mary :: Agent -- use this for "K mary ..." etc.
(julia, michael, mary) = ("julia", "michael", "mary")

solutions :: [Case]
solutions = map worldToCase $ worlds $
  initialModel `announce` annOne `announce` annTwo `announce` annThree

allCases :: [Case]
allCases = [ (Calc1,9,North)
            ,(Calc2,12,West)
            ,(Calc1,3,West)
            ,(Calc1,10,East)
            ,(Calc2,10,North)
            ,(Calc1,10,South)
            ,(Calc1,10,North)
            ,(Calc2,11,East)
            ,(Calc3,12,West)
            ,(Calc2,12,South)
            ]

propsClass :: [Int] -> Class
propsClass (x:xs)
  | x < 2 = Calc1
  | x == 2 = Calc2
  | x == 3 = Calc3
  | x > 3  = propsClass xs
propsClass _ = Calc1

propsTime :: [Int] -> Time
propsTime (x:xs)
  | x > 100 && x < 113 = x - 100
  | otherwise = propsTime xs
propsTime _ = 0

propsBuilding :: [Int] -> Building
propsBuilding [] = North
propsBuilding (x:xs)
  | x == 201 = North
  | x == 202 = East
  | x == 203 = South
  | x == 204 = West
  | otherwise  = propsBuilding xs


worldToCase :: World -> Case
worldToCase w = (propsClass (val initialModel ! w)
                ,propsTime (val initialModel ! w)
                ,propsBuilding (val initialModel ! w))

initialModel :: Model
initialModel = Mo [0,1,2,3,4,5,6,7,8,9] 
                  [(julia,[[0,2,3,5,6],[1,4,7,9],[8]])
                  ,(michael,[[0],[1,8,9],[2],[3,4,5,6],[7]])
                  ,(mary,[[0,4,6],[3,7],[5,9],[1,2,8]])] 
                  [(0,[1,109,201]),(1,[2,112,204]),(2,[1,103,204]),(3,[1,110,202]),(4,[2,110,201])
                  ,(5,[1,110,203]),(6,[1,110,201]),(7,[2,111,202]),(8,[3,112,204]),(9,[2,112,203])]

annOne, annTwo, annThree :: Form
annOne = Neg $ Con (kw julia $ P 109) (kw julia $ P 201)
annTwo = Con (Neg $ Con (kw michael $ P 1) (kw michael $ P 201)) (Neg $ Con (kw mary $ P 1) (kw mary $ P 109))
annThree = conSet [kw julia $ P 1, kw julia $ P 109, kw julia $ P 201] 

-- * Question 3: NSA Puzzle: Symbolic Solution

-- No Haskell code for this question, instead please write your
-- solution into a separate file "HW5-substitute.smcdel.txt".

-- * Question 4: Reflection

{-

The SMCDEL online tool was much easier to use for this problem because the model for the problem is identical to the Cheryl's birthday
problem in most respects. The main challenge for the simple model checker was knowing to use the 'knows whether' operator to eliminate
the relevant worlds, but the syntax and the birthday example made that choice explicit for the online tool. In general, it would be nice
for the online tool to have options for non S5 logics. As it stands, the simple model checker cannot handle different logics, but in
principle, the shift from S5 specifically would not be difficult. The SMCDEL tool would not be able to handle scenarios where the change
in knowledge is not universal, i.e., not a public announcement, which would be helpful.

-}

-- * Question 5: Speculation

{-

... write at least five sentences ...

-}

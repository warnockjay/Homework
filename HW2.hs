{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFoldable #-}
module HW2 where

-- Please do not add imports - that might break CodeGrade. When you are done with all
-- questions and get warnings about unused imports then you may and should remove them.
import Data.List
import Data.Maybe
import Test.QuickCheck

-- * Question 1: Folding

{-
Can foldl or foldr work on infinite lists?

foldr will work on an infinite list, but foldl will not. At each step, foldl recursively
calls the given function on the tail of the list, but such a program will never terminate
because (even for the fist step) it must call the function an infinite number of times
in order to return whatever value needs to be applied to the initial value. On the
other hand, foldr will eventually reach an empty foldable, and for that step, foldr has a
non-recursive value defined.

An example query and output:
GHCi> (\x _ -> x) 0 [0..]

-}

-- * Question 2: Free Theorems

-- Law:  (ff . map fun) xs == (map fun . ff) xs
ff :: [a] -> [a]
ff l = [head l]

-- Law: 
fg :: (a,b) -> a
fg (a,_) = a

-- Law:
fh :: Either a b -> Either b a
fh (Left a) = Right a
fh (Right a) = Left a

-- Law: 
fi :: [a] -> Maybe a
fi [] = Nothing
fi x = Just (head x) 

-- * Question 3: Pretty Trees

data Tree a = T a [Tree a]
  deriving (Eq,Ord,Show,Foldable)

exampleTree :: Tree Int
exampleTree = T 23 [ T 11 [ T 4 []
                          , T 7 [] ]
                   , T 12 [ T 4 []
                          , T 8 [T 3 [], T 3 [], T 2[]]] ]

indentDots :: Show a => Int -> Tree a -> String
indentDots n (T x l)= concat (replicate n ". ") ++ show x ++ "\n" ++ concatMap (indentDots (n+1)) l

ppT :: Show a => Tree a -> String
ppT (T a l) = indentDots 0 (T a l)

-- * Question 4: Arbitrary Trees

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized tree'
    where
      tree' 0 = do
        x <- arbitrary
        return (T x [])
      tree' n = do
        x <- arbitrary
        k <- choose (0, n `div` 2)
        children <- vectorOf k (tree' (n `div` 2))
        return (T x children)

-- * Question 5: Modal Logic

type World = Integer
type Universe = [World]
type Proposition = Int

type Valuation = World -> [Proposition]
type Relation = [(World,World)]

data KripkeModel = KrM Universe Valuation Relation

instance Show KripkeModel where
  show (KrM u v r) = "KrM " ++ show u ++ " " ++ vstr ++ " " ++ show r where
    vstr = "(fromJust . flip lookup " ++ show [(w, v w) | w <- u] ++ ")"

example1 :: KripkeModel
example1 = KrM [0,1,2] myVal [(0,1), (1,2), (2,1)] where
  myVal 0 = [0]
  myVal _ = [4]

example2 :: KripkeModel
example2 = KrM [0,1] myVal [(0,1), (1,1)] where
  myVal 0 = [0]
  myVal _ = [4]

data ModForm = P Proposition
             | Not ModForm
             | Con ModForm ModForm
             | Box ModForm
             | Dia ModForm
             deriving (Eq,Ord,Show)

(!) :: Relation -> World -> [World]
(!) r w = map snd (filter ((==) w . fst) r)

makesTrue :: (KripkeModel,World) -> ModForm -> Bool
makesTrue (KrM _ v _, w) (P k)     = k `elem` v w
makesTrue (m,w)          (Not f)   = not (makesTrue (m,w) f)
makesTrue (m,w)          (Con f g) = makesTrue (m,w) f && makesTrue (m,w) g
makesTrue (KrM u v r, w) (Box f)   = all (\w' -> makesTrue (KrM u v r,w') f) (r ! w)
makesTrue (KrM u v r, w) (Dia f)   = any (\w' -> makesTrue (KrM u v r,w') f) (r ! w)

tex :: ModForm -> String
tex (P k)     = "p_{" ++ show k ++ "}"
tex (Not f)   = "\\lnot " ++ tex f
tex (Con f g) = tex f ++ " \\land " ++ tex g
tex (Box f)   = "\\Box " ++ tex f
tex (Dia f)   = "\\Diamond " ++ tex f

worldsIn :: KripkeModel -> Universe
worldsIn (KrM u _ _) = u

trueEverywhere :: KripkeModel -> ModForm -> Bool
trueEverywhere m f = all (`makesTrue` f) [(m,x) | x <- worldsIn m]

instance Eq KripkeModel where
  (==) (KrM u v r) (KrM u' v' r') = all (`elem` u') u &&
                                    and [all (`elem` v' w) (v w) | w <- u] &&
                                    all (`elem` r') r

type Bisimulation = [(World,World)]

exampleBisim :: Bisimulation
exampleBisim = [(0,0), (1,1), (2,1)]

checkBisim :: KripkeModel -> KripkeModel -> Bisimulation -> Bool
checkBisim (KrM u v r) (KrM u' v' r') bi = and [all (`elem` v (fst x)) (v' (snd x)) | x <- bi] &&
                                           and [and [and [or [(w',aw') `elem` r' | w' <- u', (w,w') `elem` bi, aw' <- u', (aw,aw') `elem` bi]] | aw <- u, aw `elem` (!) r w] | w <- u] &&
                                           and [and [and [or [(w,aw) `elem` r | w <- u, (w,w') `elem` bi, aw <- u, (aw,aw') `elem` bi]] | aw' <- u', aw' `elem` (!) r' w'] | w' <- u']
type EquiRel = [[World]]

data KripkeModelS5 = KrMS5 Universe Valuation EquiRel

instance Show KripkeModelS5 where
  show (KrMS5 u v r) = "KrMS5 " ++ show u ++ " " ++ vstr ++ " " ++ show r where
    vstr = "(fromJust . flip lookup " ++ show [(w, v w) | w <- u] ++ ")"

example3 :: KripkeModelS5
example3 = KrMS5 [0,1,2] myVal [[0],[1,2]] where
  myVal 0 = [3]
  myVal 1 = [2]
  myVal _ = []

makesTrueS5 :: (KripkeModelS5, World) -> ModForm -> Bool
makesTrueS5 (KrMS5 _ v _,w) (P k)      = k `elem` v w 
makesTrueS5 (km,w) (Not f)             = not (makesTrueS5 (km,w) f)
makesTrueS5 (km,w) (Con f g)           = makesTrueS5 (km,w) f && makesTrueS5 (km,w) g
makesTrueS5 (KrMS5 u v er, w) (Box f)  = all (\w' -> makesTrueS5 (KrMS5 u v er,w') f) [aw | aw <- u, any (aw `elem`) [ws | ws <- er, w `elem` ws]]
makesTrueS5 (KrMS5 u v er,w) (Dia f)   = any (\w' -> makesTrueS5 (KrMS5 u v er,w') f) [aw | aw <- u, any (aw `elem`) [ws | ws <- er, w `elem` ws]]   

class Semantics a where
  (|=) :: (a, World) -> ModForm -> Bool 

instance Semantics KripkeModel where
  (|=) (m,w) = makesTrue (m,w)

instance Semantics KripkeModelS5 where
  (|=) (m,w) = makesTrueS5 (m,w)

instance Arbitrary ModForm where
  arbitrary = sized randomModForm
    where
    randomModForm :: Int -> Gen ModForm
    randomModForm 0 = P <$> elements [1..5]
    randomModForm n = oneof [P <$> elements [1..5]
                       , Not <$> randomModForm (n `div` 2)
                       , Con <$> randomModForm (n `div` 2)
                       <*> randomModForm (n `div` 2)
                       , Box <$> randomModForm (n `div` 2)
                       , Dia <$> randomModForm (n `div` 2)
                            ]

-- Please ensure that all generated models have a world 0.

instance Arbitrary KripkeModel where
  arbitrary = sized $ \n -> do
    ws <- vectorOf n arbitrary
    let universe = nub (0 : ws)
    valuationList <- mapM (\w -> do
                              props <- listOf arbitrary
                              return (w, props)
                           ) universe
    let valuation w = fromMaybe [] (lookup w valuationList)
    relation <- listOf $ do
                  w <- elements universe
                  w' <- elements universe
                  return (w, w')
    return (KrM universe valuation relation)

instance Arbitrary KripkeModelS5 where
  arbitrary = sized $ \n -> do
    ws <- vectorOf n arbitrary
    let universe = nub (0 : ws)
    valuationList <- mapM (\w -> do
                              props <- listOf arbitrary
                              return (w, props)
                           ) universe
    let valuation w = fromMaybe [] (lookup w valuationList)
    labels <- vectorOf (length universe) (choose (0, length universe - 1))
    let labeledWorlds = zip labels universe
        classes = groupBy (\(l1,_) (l2,_) -> l1 == l2) (sortOn fst labeledWorlds)
        equiRel = map (map snd) classes
    return (KrMS5 universe valuation equiRel)


{-
Using QuickCheck to find examples:

(i) a model that satisfies p1 ^ ~[]p2:

...

(ii) a formula that is globally true in example1 but not globally true in example2:

...

(iii) a formula that is true at 1 in example1 but not true at 1 in example3:

...
-}

tests :: [Bool]
tests = [ makesTrueS5 (example3,0) (Con (Box (P 3)) (Box (Not (P 2))))
        , (example1,1) |= Not (Box (Dia (Not (P 4))))
        ]

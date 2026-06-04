{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module HW4 where
-- * Question 1: From LensR to Lens'

type Lens' s a = forall f . Functor f => (a -> f a) -> s -> f s

data LensR s a = L { viewR :: s -> a
                   , setR :: a -> s -> s
                   , modifyR :: (a -> a) -> s -> s }

newtype Identity a = Id a
instance Functor Identity where fmap f (Id x) = Id (f x)
runIdentity :: Identity a -> a
runIdentity (Id x) = x

set :: Lens' s a -> a -> s -> s
set ln x = runIdentity . ln (Id . const x)

modify :: Lens' s a -> (a -> a) -> s -> s
modify ln f = runIdentity . ln (Id . f)

newtype Const v a = Co v
instance Functor (Const v) where fmap _ (Co x) = Co x
runConst :: Const v a -> v
runConst (Co x) = x

view :: Lens' s a -> s -> a
view ln = runConst . ln Co

lensToLensR :: Lens' s a -> LensR s a
lensToLensR ln = L { viewR = view ln
                   , setR = set ln
                   , modifyR = modify ln }

lensRtoLens :: LensR s a -> Lens' s a
lensRtoLens lnr afb s = fmap (\a -> setR lnr a s) (afb (viewR lnr s))


-- * Question 2: Manual Raise

data Person = P { name :: String, salary :: Int }  deriving (Eq, Show)

lname :: Lens' Person String
lname elt_fn (P n s) = fmap (`P` s) (elt_fn n)

lsalary :: Lens' Person Int
lsalary elt_fn (P n s) = fmap (P n) (elt_fn s)

fred :: Person
fred = P "Fred" 100

{-
  modify lsalary (+40) (P "Fred" 100)
==                                                   {def of modify}
  runIdentity (lsalary (Id . (+40)) (P "Fred" 100))
==                                                   {def of lsalary}
  runIdentity (fmap (\s' -> P "Fred" s') (Id 140))
==                                                   {def of fmap for Identity}
  runIdentity (Id (P "Fred" 140))  
==                                                   {def of runIdentity}
  P "Fred" 140
-}

-- * Question 3: ListPos to Zipper to ListPos

data ListPos a = LP [a] Int  deriving (Eq,Show)

myPos :: ListPos String
myPos = LP ["Kwik", "Kwek", "Kwak", "Tick", "Trick", "Track"] 3

data Zipper a = Zip [a] a [a] | Empty deriving (Eq,Show)

class Convertable a b where
  convert :: a -> b 

zipAppend :: Zipper a -> a -> Zipper a
zipAppend Empty _ = Empty
zipAppend (Zip l m n) x = Zip (l ++ [x]) m n 

instance Convertable (ListPos a) (Zipper a) where
  convert (LP [] _)     = Empty
  convert (LP (x:xs) 0) = Zip [] x xs
  convert (LP (x:xs) n) = zipAppend (convert (LP xs (n-1))) x

instance Convertable (Zipper a) (ListPos a) where
  convert Empty = LP [] 0
  convert (Zip l1 x l2) = LP (l1 ++ (x:l2)) (length l1) 


-- * Question 4: Tree Zip

data Tree a = Node a [Tree a]  deriving (Eq,Show)

data TreePos a = TP (Tree a) [Int]  deriving (Eq,Show)

myTree :: Tree String
myTree = Node "food" [ Node "cheese" [ Node "kaas" []
                                     , Node "Käse" [] ]
                     , Node "bread" [ Node "brood" []
                                    , Node "Brot" [] ] ]

class TreeLike t where
  -- | Create a single node.
  single :: a -> t a
  -- | Get the item at the point.
  getItem :: t a -> a
  -- | Move down to child number k.
  moveToChild :: Int -> t a -> t a
  -- | Move up to the parent, assuming we are not at the root.
  moveUp :: t a -> t a
  -- | Insert a value as a new left-most child of the point.
  insertChild :: a -> t a -> t a
  -- | Remove the point (and its subtree) and move up, assuming we are not at the root.
  remove :: t a -> t a

justTree :: TreePos a -> Tree a
justTree (TP t _) = t

instance TreeLike TreePos where
  single x = TP (Node x []) []
  getItem (TP (Node x _) [])    = x
  getItem (TP (Node _ ts) (i:is)) = getItem $ TP (ts !! i) is 
  moveToChild k (TP t ks) = TP t (ks ++ [k])
  moveUp (TP _ []) = error "Cannot move above root!"
  moveUp (TP t ks) = TP t (init ks)
  insertChild x (TP (Node n l) [])      = TP (Node n (justTree (single x) : l)) []
  insertChild x (TP (Node n ts) (i:is)) =
    let (before, after) = splitAt i ts
    in TP (Node n (before ++ [justTree (insertChild x (TP (head after) is))] ++ tail after)) (i:is) 
  remove (TP _ []) = error "Cannot remove the root node!"
  remove (TP tree (i:is)) =
    let parentPos = TP tree is
        TP (Node pval children) grandparentPath = parentPos
        newChildren = take i children ++ drop (i+1) children
    in TP (Node pval newChildren) grandparentPath


data Path a = Path a [Tree a] [Tree a]
  deriving (Eq, Show)

data ZipTree a = ZT (Tree a) (Path a)
  deriving (Eq, Show)

instance TreeLike ZipTree where
  single x = ZT (Node x []) (Path x [] [])
  
  getItem (ZT (Node x _) _) = x
  
  moveToChild k (ZT (Node v cs) (Path p leftSibs rightSibs))
    | k < 0 || k >= length cs = error "Invalid child index!"
    | otherwise =
        let (leftExtra, child:rightExtra) = splitAt k cs
        in ZT child (Path v (leftSibs ++ leftExtra) (rightExtra ++ rightSibs))
  moveToChild _ (ZT (Node _ []) _) = error "No children to move to!"
  moveUp (ZT child (Path parent leftSibs rightSibs))
    | null leftSibs && null rightSibs = error "Cannot move above root!"
    | otherwise =
        ZT (Node parent (leftSibs ++ [child] ++ rightSibs)) (Path parent [] [])
  
  insertChild x (ZT (Node v cs) path) =
    ZT (Node v (Node x [] : cs)) path
  
  remove (ZT _ (Path parent leftSibs rightSibs))
    | null leftSibs && null rightSibs = error "Cannot remove root!"
    | otherwise =
        -- Remove the current node and reassemble the parent's children as leftSibs ++ rightSibs.
        ZT (Node parent (leftSibs ++ rightSibs)) (Path parent [] [])

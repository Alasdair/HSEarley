{-# LANGUAGE TupleSections #-}
module Earley where

import Control.Applicative hiding (empty)

import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector, (!), (//))
import qualified Data.Vector as V
import qualified Data.Tree as Tree

data NTerm = S | M | T deriving (Eq, Ord, Show)

data NT n = Start | NT n (Maybe Loc) deriving (Eq, Ord)

instance Show n => Show (NT n) where
  show Start = "START"
  show (NT n (Just (a,b))) = show n ++ "[" ++ show a ++ "," ++ show b ++ "]"
  show (NT n _) = show n

data Token = Plus | Mult | One | Two deriving (Eq, Ord, Show)

type Production n t = Vector (Either (NT n) t)

showProd :: (Show n, Show t) => Production n t -> String
showProd prod = concat . intersperse " " $ map showTok (V.toList prod)
  where
    showTok (Left n) = show n
    showTok (Right t) = "<" ++ show t ++ ">"

type Loc = (Int, Int)

data Edge n t = Edge (NT n) Int Int (Production n t) deriving (Eq, Ord)

data SEdge n t = SEdge Loc (NT n) Int Int (Production n t)

toEdge :: SEdge n t -> Edge n t
toEdge (SEdge c n dot i prod) = Edge n dot i prod

toSEdge :: Loc -> Edge n t -> SEdge n t
toSEdge c (Edge n dot i prod) = SEdge c n dot i prod

instance (Eq n, Eq t) => Eq (SEdge n t) where
    a == b = toEdge a == toEdge b

instance (Ord n, Ord t) => Ord (SEdge n t) where
    compare a b = compare (toEdge a) (toEdge b)

instance (Show n, Show t) => Show (Edge n t) where
    show (Edge n dot i prod) = show n ++ " -> " ++ showProd (V.take dot prod) ++ " . " ++ showProd (V.drop dot prod) ++ " (" ++ show i ++ ")"

instance (Show n, Show t) => Show (SEdge n t) where
    show (SEdge c n dot i prod) = show c ++ " : " ++ show n ++ " -> " ++ showProd (V.take dot prod) ++ " . " ++ showProd (V.drop dot prod) ++ " (" ++ show i ++ ")"

printChart chart = mapM_ (\(n, x) -> putStrLn ("S(" ++ show n ++ ")") >> print x) $ zip [0..] (V.toList chart)

type Grammar n t = Map (NT n) (Set (Production n t))

-- Get the rules for a non-terminal n in the grammar.
rules :: Ord n => NT n -> Grammar n t -> Set (Production n t)
rules n grammar = grammar Map.! n

data ParseTree n t = Leaf t
                   | Node n [ParseTree n t] deriving (Show)

-- A chart is a vector of state sets. We write S(n) to mean chart ! n,
-- for some chart which implied by the context.
type Chart n t = Vector (StateSet n t)

-- | A state set is essentially a queue containing edges, however, we
-- do not guarantee that it is FIFO. Edges are removed in an arbitrary
-- order, based on their Ord instance. When items are dequeued, they
-- are kept by the data structure in a passive set. Items still in the
-- queue are considered active.
data StateSet n t = StateSet
    { passive :: Set (SEdge n t)
      -- ^ Get the passive edges
    , active :: Set (SEdge n t)
      -- ^ Get the active edges
    , counter :: Int
    }

-- | An edge is a member of a state set if it is either a passive or
-- active edge.
member :: (Ord n, Ord t) => Edge n t -> StateSet n t -> Bool
member edge (StateSet p a c) = Set.member edge (Set.map toEdge p) || Set.member edge (Set.map toEdge a)

instance (Ord n, Show n, Ord t, Show t) => Show (StateSet n t) where
    show s@(StateSet p a _) = concatMap (\x -> show x ++ "\n") (Set.elems (passive s `Set.union` a))

-- | Create an empty state set.
empty :: StateSet n t
empty = StateSet Set.empty Set.empty 0

-- | Dequeue an edge from the state set S(i).
dequeue :: (Ord n, Ord t) => Int -> Chart n t -> Maybe (SEdge n t, Chart n t)
dequeue i chart =
    case dequeue' (chart ! i) of
      Nothing -> Nothing
      Just stateSet -> Just (fst stateSet, chart // [(i, snd stateSet)])

-- | Enqueue a set of edges to the state set S(i)
enqueue :: (Ord n, Ord t) => Int -> [Edge n t] -> Chart n t -> Chart n t
enqueue i edges chart =
    chart // [(i, StateSet p (a `Set.union` (Set.filter (`Set.notMember` p) sedges)) (c + Set.size sedges))]
  where
    sedges = Set.fromList $ map (uncurry toSEdge) $ zip (map (i,) (enumFrom c)) edges

    p = passive (chart ! i)
    a = active (chart ! i)
    c = counter (chart ! i)

dequeue' :: (Ord n, Ord t) => StateSet n t -> Maybe (SEdge n t, StateSet n t)
dequeue' (StateSet passive active c) =
    case Set.minView active of
      Nothing -> Nothing
      Just (a, as) -> Just (a, StateSet (Set.insert a passive) as c)

mkChart :: (Ord n, Ord t) => n -> Vector t -> Chart n t
mkChart start words = enqueue 0 [Edge Start 0 0 (V.singleton (Left (NT start Nothing)))] emptyChart
  where
    emptyChart = V.replicate (V.length words + 1) empty

tgram :: Grammar NTerm Token
tgram = Map.fromList
    [ (NT S Nothing, Set.fromList [V.fromList [Left (NT S Nothing), Right Plus, Left (NT S Nothing)], V.singleton (Left (NT M Nothing))])
    , (NT M Nothing, Set.fromList [V.fromList [Left (NT M Nothing), Right Mult, Left (NT T Nothing)], V.singleton (Left (NT T Nothing))])
    , (NT T Nothing, Set.fromList (map (V.singleton . Right) [One, Two]))
    ]

iter :: (a -> Maybe a) -> a -> a
iter f a = case f a of
             Nothing -> a
             Just a' -> iter f a'

isComplete :: SEdge n t -> Bool
isComplete (SEdge _ _ dot _ prod) = dot == V.length prod

earley' :: (Ord n, Ord t) => Int -> Vector t -> Grammar n t -> Chart n t -> Maybe (Chart n t)
earley' j words grammar chart =
    case dequeue j chart of
      Nothing -> Nothing
      Just (edge@(SEdge _ n dot i prod), chart')
        | isComplete edge                -> Just $ complete edge chart'
        | Left nonTerminal <- prod ! dot -> Just $ predict nonTerminal chart'
        | Right terminal <- prod ! dot   -> Just $ scan terminal edge chart'
  where
    predict n chart = enqueue j (Edge n 0 j <$> Set.toList (rules n grammar)) chart

    scan terminal edge chart
      | j == V.length words   = chart -- Avoid creating rules off the end of the chart.
      | words ! j == terminal = enqueue (j + 1) [shift edge] chart
      | otherwise             = chart

    complete (SEdge c n dot i prod) chart =
        let edges = Set.elems $ passive (chart ! i) `Set.union` active (chart ! i)
        in enqueue j (complete' edges) chart
      where
        complete' [] = []
        complete' (edge@(SEdge _ _ dot _ prod):edges)
          | isComplete edge = complete' edges
          | Left nonTerminal <- prod ! dot, nonTerminal == n = addLoc dot c (shift edge) : complete' edges
          | otherwise = complete' edges

    shift (SEdge _ n dot i prod) = Edge n (dot + 1) i prod

    addLoc dot loc (Edge n dot' i prod) = Edge n dot' i (prod // [(dot, addLoc' loc (prod ! dot))])
      where
        addLoc' loc (Left (NT a _)) = Left (NT a (Just loc))
        addLoc' _ x = x

earley :: (Ord n, Ord t) => n -> Grammar n t -> Vector t -> Chart n t
earley start grammar words =
    foldl (\c n -> iter (earley' n words grammar) c) (mkChart start words) [0..(V.length  words)]

getForest :: (Ord n, Ord t) => Chart n t -> [ParseTree n t]
getForest chart = startTree <$> completeParses chart
  where
    completeParse edge@(SEdge _ Start _ _ _) = isComplete edge
    completeParse _ = False

    completeParses = Set.toList . Set.filter completeParse . passive . V.last

    startTree (SEdge _ Start _ _ prod) = symTree (V.head prod)

    sedgeTree (SEdge _ Start _ _ _) = error "Unexpected start on left!"
    sedgeTree (SEdge _ (NT n _) _ _ prod) = Node n $ V.toList $ V.map symTree prod

    symTree (Left Start) = error "Unexpected start on right!"
    symTree (Right t) = Leaf t
    symTree (Left (NT n Nothing)) = error "Incomplete parse tree!"
    symTree (Left (NT n (Just (x,y)))) = sedgeTree (getEdge x y)

    getEdge x y = Set.findMin . Set.filter (isEdge y) $ passive (chart ! x)

    isEdge n (SEdge (_,m) _ _ _ _) = n == m

toDisplayTree :: (Show n, Show t) => ParseTree n t -> Tree.Tree String
toDisplayTree (Node n children) = Tree.Node (show n) $ map toDisplayTree children
toDisplayTree (Leaf t) = Tree.Node (show t) []

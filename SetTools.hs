module SetTools where

import Data.HashSet (HashSet) --unordered-containers
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set

setBind :: (Hashable s1, Hashable s2, Eq s1, Eq s2) => HashSet s1 -> (s1 -> HashSet s2) -> HashSet s2
setBind s f = foldl (Set.union) Set.empty $ Set.map f s
--I can't make a monad instance because of the type constraints on what goes into the set.

powerSet :: (Hashable a, Eq a) => HashSet a -> HashSet (HashSet a)
powerSet mySet = Set.fromList $ map Set.fromList (powerSetList (Set.toList mySet))

powerSetList :: [a] -> [[a]]
powerSetList [] = [[]]
powerSetList (x:xs) = tailSet ++ map (x:) tailSet
    where tailSet = powerSetList xs

cartesianProduct :: (Hashable s1, Hashable s2, Eq s1, Eq s2) =>  HashSet s1 -> HashSet s2 -> HashSet (s1, s2)
cartesianProduct s1 s2 = s1 `setBind` (\e1 -> Set.map (\e2 -> (e1, e2)) s2)

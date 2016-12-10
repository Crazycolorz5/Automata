module SetTools where

setBind :: (Hashable s1, Hashable s2, Eq s1, Eq s2) => HashSet s1 -> (s1 -> HashSet s2) -> HashSet s2
setBind s f = foldl (Set.union) Set.empty $ Set.map f s

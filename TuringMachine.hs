module TuringMachine where

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set

data Configuration state tape = C state [Maybe tape] [Maybe tape] --Representing the left side and the right side of the tape. Nothing represents blank.
newtype TM state tape = TM (HashSet state, HashSet tape, HashSet tape, state->Maybe tape->(state, Maybe tape, Direction), state, state, state)
--Representing states, input alphabet, tape alphabet, delta, starting state, failure state, accepting state
data Direction = L | R

tmAccepts :: (Hashable state, Hashable tape, Eq state, Eq tape) => TM state tape -> [tape] -> Bool
--Repeatedly apply delta until we reach an accepting or failure state.
tmAccepts (TM (states, alpha, tapeAlpha, delta, start, failing, accepting)) string = finalQ == accepting 
    where
        iterateUntil f i p = if p i then i else iterateUntil f (f i) p --Since non-halting is a thing, this must as a while/until structure.
        startConfiguration = C start [] (map Just string ++ repeat Nothing)
        configDelta (C q l (r:rs)) = let (newQ, newR, dir) = delta q r in case dir of
                                         L -> if null l 
                                                then C newQ [] (newR:rs) 
                                                else let (lastL:ls) = l in C newQ ls (lastL:newR:rs)
                                         R -> C newQ (newR:l) rs
        (C finalQ l r) = iterateUntil configDelta startConfiguration (\(C q _ _) -> q == failing || q == accepting)

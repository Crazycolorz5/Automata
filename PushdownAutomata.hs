module PushdownAutomata where

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set

newtype PDA state alphabet stack = PDA (HashSet state, HashSet alphabet, HashSet stack, state->Maybe alphabet->stack->(state, [stack]), state, HashSet state)


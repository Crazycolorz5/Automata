module PushdownAutomata where

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set
import SetTools

newtype PDA state alphabet stack = PDA (HashSet state, HashSet alphabet, HashSet stack, state->Maybe alphabet->Maybe stack->HashSet (state, [stack]), state, HashSet state)

applyEpsilon :: (Hashable state, Hashable stack) => state -> stack -> (state->Maybe alphabet->Maybe stack->HashSet (state, [stack])) -> HashSet (state, [stack])
applyEpsilon state stack delta = let withoutStack = delta state Nothing Nothing in
                            if not (null stack) then Set.union withoutStack (delta state Nothing (head stack)) else withoutStack

epsilonStar :: (Hashable state, Hashable stack) => state -> [stack] -> (state->Maybe alphabet->Maybe stack->HashSet (state, [stack])) -> HashSet (state, [stack])

applyPDA :: (Hashable a, Hashable b, Hashable c) => PDA a b c -> [b] -> Bool
applyPDA pda string = foldl 



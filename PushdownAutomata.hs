module PushdownAutomata where

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set
import SetTools
import Control.Arrow

newtype PDA state alphabet stack = PDA (HashSet state, HashSet alphabet, HashSet stack, state->Maybe alphabet->Maybe stack->HashSet (state, Maybe stack), state, HashSet state)
newtype CFGRule variable terminal = Rule (variable, [Either variable terminal])
newtype CFG variable terminal = Grammar (HashSet variable, HashSet terminal, [CFGRule variable terminal], variable)
data CNFRule variable terminal = CNFRule (variable, Either (variable, variable) terminal) | EmptyRule --EmptyRule represents the rule S -> epsilon
newtype CNFCFG variable terminal = CNFGrammar (HashSet variable, HashSet terminal, [CNFRule variable terminal], variable)

pdaDelta (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = delta
pdaStates (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = states
hasSingleTerminalState (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = Set.size finalStates == 1

--Okay, so I wanted to do running a PDA similar to how I did a FSA, but that doesn't quite work -- 
--The epsilon transitions don't eventually stabilize, since we could have an epsilon transition self-loop that adds some number of things from the stack
--Results in, essentially, a* being on the stack. Having a series of these among states can also lead to more complex RLs on the stack.
-- (In fact: Conjecture, the stack of a PDA can be described with a regular language... at least?)
{-


applyEpsilon :: (Hashable state, Hashable stack) => state -> stack -> (state->Maybe alphabet->Maybe stack->HashSet (state, [stack])) -> HashSet (state, [stack])
applyEpsilon state stack delta = let withoutStack = delta state Nothing Nothing in
                            if not (null stack) then Set.union withoutStack (delta state Nothing (head stack)) else withoutStack

epsilonStar :: (Hashable state, Hashable stack) => state -> [stack] -> (state->Maybe alphabet->Maybe stack->HashSet (state, [stack])) -> HashSet (state, [stack])

applyPDA :: (Hashable a, Hashable b, Hashable c) => PDA a b c -> [b] -> Bool
applyPDA pda string = foldl 


-}

--Instead, I'm going to have to basically code a BFS with this
--However, this makes it only RECOGNIZE, since if it can't accept, I may be stuck in an infinite episilon transition loop...
{-

type PDAState state alphabet stack = (state, [alphabet], [stack])
applyPDA :: (Hashable a, Hashable b, Hashable c) => PDA a b c -> [b] -> Bool
applyPDA pda string = where
    firstInstance p l = case dropWhile (not . p) l of
                             [] -> Nothing
                             (x:xs) -> Just x
    bfsStep :: Queue 
    
-}
    

--Okay, let's do it with the algorithm proposed but not covered in class, (A_pda)
--Turn the PDA to a CNF Grammar, then I can predictably generate strings (and more importantly, prove termination).

{-
P = (Q, ∑, S, δ, q0, I, F
Step 1 	For every w, x, y, z ∈ Q, m ∈ S and a, b ∈ ∑, if δ (w, a, ε) contains (y, m) and (z, b, m) contains (x, ε), add the production rule Xwx → a Xyz b in grammar G.
Step 2 	For every w, x, y, z ∈ Q, add the production rule Xwx → XwyXyx in grammar G.
Step 3 	For w ∈ Q, add the production rule Xww → ε in grammar G.
Source: https://www.tutorialspoint.com/automata_theory/pda_context_free_grammar.htm (It's mislabeled at the bottom)
-}
--first, write a method for converting a PDA with multiple terminal states to just one.
condenseFinalStates :: (Hashable state, Hashable alphabet, Hashable stack, Eq state, Eq alphabet, Eq stack) => PDA state alphabet stack -> PDA (Maybe state) alphabet stack
condenseFinalStates (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = PDA (newStates, sigma, stackAlpha, newDelta, Just startState, Set.singleton Nothing) where
    newStates = Set.insert Nothing $ Set.map Just states --Join the "Nothing" state to an elevated version of states 
    newDelta Nothing _ _ = Set.empty
    newDelta (Just s) Nothing sTop = let normalResult = Set.map (first Just) $ delta s Nothing sTop in
                                   if Set.member s finalStates
                                      then Set.insert (Nothing, sTop) normalResult --Add an epsilon transition to the distinguished state
                                      else normalResult
    newDelta (Just s) a sTop = Set.map (first Just) $ delta s a sTop
    -- :: state->Maybe alphabet->Maybe stack->HashSet (state, Maybe stack)

--Turning step 1 "backwards", one can show that the rule come from a unique arrow.
pdaToCFG :: (Hashable state, Hashable alphabet, Hashable stack, Eq state, Eq alphabet, Eq stack) =>  PDA state alphabet stack -> CFG (Maybe state, Maybe state) alphabet
pdaToCFG pda = Grammar (cartesianProduct states states, sigma, rules, (startState, Nothing))
    where
        PDA (states, sigma, stackAlpha, delta, startState, finalStates) = condenseFinalStates pda
        rules = step1 ++ step2 ++ step3
        statesList = Set.toList states
        step1 = do
            w <- statesList
            x <- statesList
            y <- statesList
            z <- statesList
            m <- Nothing : (map Just $ Set.toList stackAlpha) --Consider the epsilon case as well
            a <- Nothing : (map Just $ Set.toList sigma) -- same
            let a' = case a of Nothing -> []; Just x -> [Right x]
            b <- Nothing : (map Just $ Set.toList sigma)
            let b' = case b of Nothing -> []; Just x -> [Right x]
            if ((y, m) `Set.member` delta w a Nothing) && ((x, Nothing) `Set.member` delta z b m)
               then return $ Rule ((w, x), a' ++ [Left (y, z)] ++ b')
               else []
        step2 = [Rule ((w,x), [Left (w,y), Left (y,x)]) | w <- statesList, x <- statesList, y <- statesList, z <- statesList]
        step3 = [Rule ((w,w), []) | w <- statesList]

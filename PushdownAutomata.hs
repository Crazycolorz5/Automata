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

--pdaDelta (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = delta
--pdaStates (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = states
--hasSingleTerminalState (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = Set.size finalStates == 1

instance (Show variable, Show terminal) => Show (CFGRule variable terminal) where
    show (Rule (var, l)) = show var ++ " -> " ++ case l of [] -> "epsilon"; otherwise -> foldl1 (\acc e -> acc ++ ' ':e) (map (either show show) l)

instance (Show variable, Show terminal) => Show (CFG variable terminal) where
    show (Grammar (vars, terms, rules, start)) = "Variables: " ++ show vars ++ "\nTerminals: " ++ show terms ++ "\nRules:" ++ foldl (\acc e->acc ++ '\n':(show e)) "" rules ++ "\nStarting Variable: " ++ show start

--Okay, let's do it with the algorithm proposed but not covered in class, (A_pda)
--Turn the PDA to a CNF Grammar, then I can predictably generate strings (and more importantly, prove termination).

{-
P = (Q, ∑, S, δ, q0, I, F
Step 1 	For every w, x, y, z ∈ Q, m ∈ S and a, b ∈ ∑, if δ (w, a, ε) contains (y, m) and (z, b, m) contains (x, ε), add the production rule Xwx → a Xyz b in grammar G.
Step 2 	For every w, x, y, z ∈ Q, add the production rule Xwx → XwyXyx in grammar G.
Step 3 	For w ∈ Q, add the production rule Xww → ε in grammar G.
Source: https://www.tutorialspoint.com/automata_theory/pda_context_free_grammar.htm (It's mislabeled at the bottom)

better source, with fewer errors: http://www.csee.umbc.edu/~chang/cs451.f08/pda2cfg.pdf
I think I understand what this is saying. A_ij represents some way that we can get to j from i.
So clearly, we want to solve from A_start,end
And if we're at i, and want to get to j, and know a way to get to k from i and from k to j, clearly we can get from i to j through A_ik A_kj
The last, most complex rules, are for out real transitions -- but basically it matches each push with its respective pop.
-}
--first, write a method for converting a PDA with multiple terminal states to just one.
condenseFinalStates :: (Hashable state, Hashable alphabet, Hashable stack, Eq state, Eq alphabet, Eq stack) => PDA state alphabet stack -> PDA (Maybe state) alphabet stack
condenseFinalStates (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = PDA (newStates, sigma, stackAlpha, newDelta, Just startState, Set.singleton Nothing) where
    newStates = Set.insert Nothing $ Set.map Just states --Join the "Nothing" state to an elevated version of states 
    newDelta Nothing _ _ = Set.empty
    newDelta (Just s) Nothing Nothing = let normalResult = Set.map (first Just) $ delta s Nothing Nothing in
                                   if Set.member s finalStates
                                      then Set.insert (Nothing, Nothing) normalResult --Add an epsilon transition to the distinguished state
                                      else normalResult
    newDelta (Just s) a sTop = Set.map (first Just) $ delta s a sTop
    -- :: state->Maybe alphabet->Maybe stack->HashSet (state, Maybe stack)

--The "Nothing" variable is the starting state.
pdaToCFG :: (Hashable state, Hashable alphabet, Hashable stack, Eq state, Eq alphabet, Eq stack) =>  PDA state alphabet stack -> CFG (Maybe (state, state)) alphabet
pdaToCFG (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = Grammar (variables, sigma, rules, Nothing)
    where
        variables = Set.insert Nothing $ Set.map Just $ cartesianProduct states states
        rules = fromStart ++ transitions ++ paths ++ identity
        statesList = Set.toList states
        fromStart = Set.foldl' (\acc e -> Rule (Nothing, [Left (Just (startState, e))]) : acc) [] finalStates
        transitions = do
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
               then return $ Rule (Just (w, x), a' ++ [Left (Just (y, z))] ++ b')
               else []
        paths = [Rule (Just (i,j), [Left (Just (i,k)), Left (Just (j, k))]) | i <- statesList, j <- statesList, k <- statesList]
        identity = [Rule (Just (w,w), []) | w <- statesList]


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
    

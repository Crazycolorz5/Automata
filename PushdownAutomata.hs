{-# LANGUAGE DeriveGeneric #-}
module PushdownAutomata where

import GHC.Generics (Generic)
import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set
import SetTools
import Control.Arrow

newtype PDA state alphabet stack = PDA (HashSet state, HashSet alphabet, HashSet stack, state->Maybe alphabet->Maybe stack->HashSet (state, Maybe stack), state, HashSet state)
newtype CFGRule variable terminal = Rule (variable, [Either variable terminal]) deriving (Eq, Generic)
instance (Hashable variable, Hashable terminal) => Hashable (CFGRule variable terminal)
newtype CFG variable terminal = Grammar (HashSet variable, HashSet terminal, HashSet (CFGRule variable terminal), variable)
data CNFRule variable terminal = CNFRule (variable, Either (variable, variable) terminal) | EmptyRule deriving (Eq, Generic) --EmptyRule represents the rule S -> epsilon
instance (Hashable variable, Hashable terminal) => Hashable (CNFRule variable terminal)
    --Note that these a list of these rules does not imply that the language is in CNF.
    --Namely, you can have rules to produce the start variable again.
    --I could enforce this on the type level by introducing Maybe and having the start variable be forced to be Nothing,
    --But not only is that constraining, it also breaks the definition of CNF CFG (as it'd just be a 3 tuple).
    --However, it COULD BE DONE is what I'm arguing.
newtype CNFCFG variable terminal = CNFGrammar (HashSet variable, HashSet terminal, HashSet (CNFRule variable terminal), variable)

instance (Show variable, Show terminal) => Show (CFGRule variable terminal) where
    show (Rule (var, l)) = show var ++ " -> " ++ case l of [] -> "epsilon"; otherwise -> foldl1 (\acc e -> acc ++ ' ':e) (map (either show show) l)

instance (Show variable, Show terminal) => Show (CFG variable terminal) where
    show (Grammar (vars, terms, rules, start)) = "Variables: " ++ show vars ++ "\nTerminals: " ++ show terms ++ "\nRules:" ++ foldl (\acc e->acc ++ '\n':(show e)) "" rules ++ "\nStarting Variable: " ++ show start
instance (Show variable, Show terminal) => Show (CNFRule variable terminal) where
    show EmptyRule = "Start -> epsilon"
    show (CNFRule (v, Left (v1, v2))) = show v ++ " -> " ++ show v1 ++ " " ++ show v2
    show (CNFRule (v, Right t)) = show v ++ " -> " ++ show t
instance (Show variable, Show terminal) => Show (CNFCFG variable terminal) where
    show (CNFGrammar (vars, terms, rules, start)) = "Variables: " ++ show vars ++ "\nTerminals: " ++ show terms ++ "\nRules:" ++ foldl (\acc e->acc ++ '\n':(show e)) "" rules ++ "\nStarting Variable: " ++ show start

--Okay, let's do it with the algorithm proposed but not covered in class, (A_pda)
--Turn the PDA to a CNF Grammar, then I can predictably generate strings (and more importantly, prove termination).
pdaToCNFCFG :: (Hashable state, Hashable alphabet, Hashable stack, Eq state, Eq alphabet, Eq stack) => PDA state alphabet stack -> CNFCFG (CNFVariable (Maybe (state, state)) alphabet) alphabet
pdaToCNFCFG = cfgToCNFCFG . pdaToCFG --Put this here, functions defined below.

--Of course, the downside is that this algorithm runs in about (q^3)^l time... 
--where q is the number of states in the PDA and l is the length of the string to recognize...

--Not to mention the time to construct the CNF CFG...
{-
Source: https://www.tutorialspoint.com/automata_theory/pda_context_free_grammar.htm (It's mislabeled at the bottom)

Better source, with fewer errors: http://www.csee.umbc.edu/~chang/cs451.f08/pda2cfg.pdf
I think I understand what this is saying. A_ij represents some way that we can get to j from i.
So clearly, we want to solve from A_start,end
And if we're at i, and want to get to j, and know a way to get to k from i and from k to j, clearly we can get from i to j through A_ik A_kj
The last, most complex rules, are for out real transitions -- but basically it matches each push with its respective pop.
-}

--The "Nothing" variable is the starting state.
pdaToCFG :: (Hashable state, Hashable alphabet, Hashable stack, Eq state, Eq alphabet, Eq stack) =>  PDA state alphabet stack -> CFG (Maybe (state, state)) alphabet
pdaToCFG (PDA (states, sigma, stackAlpha, delta, startState, finalStates)) = Grammar (variables, sigma, rules, Nothing)
    where
        deltaPrime state Nothing Nothing = Set.insert (state, Nothing) $ delta state Nothing Nothing --Always allow nullary epsilon transitions back to a state
        deltaPrime q a s = delta q a s
        variables = Set.insert Nothing $ Set.map Just $ cartesianProduct states states
        rules = Set.fromList $ fromStart ++ transitions ++ paths ++ identity
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
            if ((y, m) `Set.member` deltaPrime w a Nothing) && ((x, Nothing) `Set.member` deltaPrime z b m)
               then return $ Rule (Just (w, x), a' ++ [Left (Just (y, z))] ++ b')
               else []
        paths = [Rule (Just (i,j), [Left (Just (i,k)), Left (Just (k, j))]) | i <- statesList, j <- statesList, k <- statesList]
        identity = [Rule (Just (w,w), []) | w <- statesList]

--Now, I must recreate the algorithm for turning a CFG to a CNFCFG
--https://people.cs.clemson.edu/~goddard/texts/theoryOfComputation/9a.pdf source
data CNFVariable variable terminal = NewVar Integer | OldVar variable | LiftedTerm terminal deriving (Eq, Show, Generic) --Use Integer for arbitrary number of new variables.
instance (Hashable variable, Hashable terminal) => Hashable (CNFVariable variable terminal)

cfgToCNFCFG :: (Hashable variable, Eq variable, Hashable terminal, Eq terminal) => CFG variable terminal -> CNFCFG (CNFVariable variable terminal) terminal
cfgToCNFCFG (Grammar (vars, terms, rulesSet, start)) = CNFGrammar (newVars, terms, newRules, OldVar start) where
    rules = Set.toList rulesSet
    --Step 1 : Remove rules ending in epsilon.
    directlyNullableVariables = Set.foldl' (\acc (Rule (v, l)) -> if null l then Set.insert v acc else acc) Set.empty rulesSet --Those that produce null directly
    nullableVariables = fixedPoint $ iterate producingOnly directlyNullableVariables where --All variables that can eventually produce epsilon.
        producingOnly vars = Set.map (\(Rule (v,l)) -> v) $ Set.filter (\(Rule (v,l)) -> all (flip Set.member . Set.map Left $ vars) l) rulesSet
        fixedPoint (x:y:z) = if x == y then x else fixedPoint (y:z)
    eliminatedNullables = filter (\(Rule (v,l)) -> v == start || not (null l)) $ do --Avoid eliminating S->epsilon afterwards.
        Rule (v,l) <- rules --For every rule
        map (\e -> Rule (v, e)) (expand l nullableVariables) where --Expand its rhs's expansion with respect to the nullable variables
            expand [] wrt = [[]]
            expand ((Left x):xs) wrt = let without = expand xs wrt in 
                                           if x `elem` wrt 
                                              then map (Left x:) without ++ without --Similar to programming for a powerset. But on branch if it's in the wrt list.
                                              else map (Left x:) without
            expand ((Right x):xs) wrt = map (Right x:) $ expand xs wrt
    --Step 2: Eliminate variable-unit productions.
    eliminatedVariableUnits = Set.fromList $ do
        Rule (v, l) <- eliminatedNullables
        case l of
            ((Left x):[]) -> performSubstitution v [v] x where  --If the rule is a unit, sub it with all of the target's rules
                performSubstitution var traversed current = let relevants = filter (\(Rule (v,l)) -> v == current) eliminatedNullables in do --This is done recursively along all unit productions.
                    Rule (vin, lin) <- relevants
                    case lin of
                         ((Left x):[]) -> if x `elem` traversed then [] else performSubstitution var (current:traversed) x --However, if we've seen it before (in this expansion), no need to expand it.
                         otherwise -> return $ Rule (var, lin)
            otherwise -> return $ Rule (v, l)
    --Step 3: Elimate long expressions by introducing new variables.
    -- The difficulty lies in keeping track of unique variables to introduce.
    (nUsed, eliminatedLongExpresssons) = foldl (\(i, accL)->(\(r@(Rule (v,l)))->if length l <= 2 
                                                                          then (i, Set.insert (Rule (OldVar v, map (left OldVar) l)) accL)
                                                                          else let (iNext, lNext) = introduceNewVars i r in (iNext, lNext `Set.union` accL))) (0, Set.empty) eliminatedVariableUnits where
        introduceNewVars next (Rule (v, l)) = expandRules next (OldVar v) l
        expandRules next vCur (l@(l1:ls))
            | length l == 2 = (next, Set.singleton $ Rule (vCur, map (left OldVar) l))
            | otherwise     = let (tailNext, rs) = expandRules (succ next) (NewVar next) ls in (tailNext,Set.insert (Rule (vCur, left OldVar l1:Left (NewVar next):[])) rs)

    --Step 4: Lift all terminals.
    eliminatedMixedTerminals = Set.map (\term -> Rule (LiftedTerm term, [Right term])) terms `Set.union` Set.map (\(Rule (v, l)) -> case l of --Rules for production of terminals, plus
             ((Right term):[]) -> Rule (v, l) --If it's JUST a terminal, it can stay.
             otherwise -> Rule (v, map (\x -> case x of Right term -> Left (LiftedTerm term); otherwise -> x) l)) eliminatedLongExpresssons
    
    --Now perform translation into CNF
    newRules = flip Set.map eliminatedMixedTerminals $ \(Rule (v, l)) -> case l of
                                        [] -> case v of OldVar vOld -> if vOld == start then EmptyRule else error "Epsilon transition for non-start variable."; otherwise -> error "Epsilon transition for new variable."
                                        ((Left v1):(Left v2):[]) -> CNFRule (v, Left (v1, v2))
                                        ((Right t):[]) -> CNFRule (v, Right t)
                                        otherwise -> error $ "Bad rule."
    newVars = Set.fromList (take (fromIntegral nUsed) $ fmap NewVar [0..]) `Set.union` Set.map OldVar vars `Set.union` Set.map LiftedTerm terms

    
cnfcfgProduces :: (Hashable variable, Hashable terms, Eq variable, Eq terms) => CNFCFG variable terms -> [terms] -> Bool
cnfcfgProduces (CNFGrammar (vars, terms, rules, start)) str = if null str then EmptyRule `elem` rules else map Right str `elem` ((iterate (>>= (applyRules start rules)) [[Left start]]) !! (2 * (length str) - 1)) 

applyRules _ _ [] = []
applyRules start rules (s:ss) = case s of
             Left var -> map (s:) (applyRules start rules ss) ++ map (++ss) (Set.toList . Set.map getReplacement . Set.filter (involvesVar start var) $ rules) --We can choose to replace s, or not to replace s.
             otherwise -> map (s:) $ applyRules start rules ss
        where
    involvesVar start var rule = case rule of EmptyRule -> var == start; CNFRule (var', _) -> var == var'
    getReplacement rule = case rule of EmptyRule -> []; CNFRule (var, Left (v1, v2)) -> [Left v1,Left v2]; CNFRule (var, Right t) -> [Right t]
    
--Old, previous thoughts on seeing if a PDA accepted a string:
--The BFS thought probably has the most practicality for recognition, even if it won't decide the acceptance problem.

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
    

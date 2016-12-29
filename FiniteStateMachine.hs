module FiniteStateMachine where

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set
import Data.Foldable (Foldable, foldl)
import Prelude hiding (foldl)
import SetTools

--Deterministic
newtype FSM state alphabet = FSM (HashSet state, HashSet alphabet, state->alphabet->state, state, HashSet state)
--(Q, Sigma, delta, q0, F)
newtype NDFSM state alphabet = NDFSM (HashSet state, HashSet alphabet, state->Maybe alphabet->HashSet state, state, HashSet state)

transition (FSM (q, sigma, delta, q0, f)) = delta
start (FSM (q, sigma, delta, q0, f)) = q0
acceptedStates (FSM (q, sigma, delta, q0, f)) = f

startND (NDFSM (q, sigma, delta, q0, f)) = q0
transitionND (NDFSM (q, sigma, delta, q0, f)) = delta
acceptedNDStates (NDFSM (q, sigma, delta, q0, f)) = f

--Running FSMs
applyFSM :: (Hashable s, Eq s, Foldable f) => FSM s a -> f a -> Bool
applyFSM fsm str = foldl (transition fsm) (start fsm) str `Set.member` (acceptedStates fsm)

applyNDFSM :: (Hashable s, Eq s, Foldable f) => NDFSM s a -> f a -> Bool
applyNDFSM fsm str = any (flip Set.member (acceptedNDStates fsm)) allFinalStates
    where
        appliedInitialEpsilon = untilStableEpsilons (Set.singleton $ startND fsm) (transitionND fsm)
        allFinalStates = foldl (\acc e->(acc `setBind` flip (transitionND fsm) (Just e)) `untilStableEpsilons` (transitionND fsm)) appliedInitialEpsilon str

--Converting detministic to non-deterministic and back

ndfsmToFSM :: (Hashable s, Eq s) => NDFSM s a -> FSM (HashSet s) a
ndfsmToFSM (NDFSM (q, sigma, delta, q0, f)) = FSM (newQ, sigma, newDelta, newq0, newf)
    where
        newQ = powerSet q
        newq0 = untilStableEpsilons (Set.singleton $ q0) (delta)
        newDelta stateSet a = stateSet `setBind` flip delta (Just a) `untilStableEpsilons` (delta)
        newf = Set.filter (not . null . Set.intersection f) $ newQ -- set of all sets that contain an element of f.
        -- take all state sets, take the ones whose intersections with f are not empty.


fsmToNDFSM :: (Hashable s, Eq s) => FSM s a -> NDFSM s a
fsmToNDFSM (FSM (q, sigma, delta, q0, f)) = NDFSM (q, sigma, delta', q0, f) where 
        delta' state alpha = case alpha of
            (Just a) -> Set.singleton (delta state a)
            Nothing -> Set.empty
            
            
applySingleEpsilonTransition::(Hashable s, Eq s) => HashSet s -> (s -> Maybe a -> HashSet s) -> HashSet s
applySingleEpsilonTransition set trans = set `setBind` (\e -> Set.insert e (flip trans Nothing e))
{- 
Thought (justifying inserting e): Suppose we have an NDFSM m. If we construct m' by adding an epsilon transition that is a self-loop to every state,
    then the language described by m = the language described by m'
-}
untilStableEpsilons::(Hashable s, Eq s) => HashSet s -> (s -> Maybe a -> HashSet s) -> HashSet s
untilStableEpsilons set trans = case takeWhile (uncurry (/=)) (zip transformations (tail transformations)) of
    [] -> set
    x -> snd . last $ x
    where
        transformations = iterate (flip applySingleEpsilonTransition trans) set

--Operations on FSMs
union::(Hashable s1, Hashable s2, Eq s1, Eq s2) => FSM s1 a -> FSM s2 a -> FSM (s1, s2) a
union (FSM (q1, sigma1, delta1, q0, f1)) (FSM (q2, sigma2, delta2, q0', f2)) = FSM (cartesianProduct q1 q2, sigma1, \(s1,s2)->(\a->(delta1 s1 a, delta2 s2 a)), (q0, q0'), Set.union (cartesianProduct f1 q2) (cartesianProduct q1 f2))

intersection::(Hashable s1, Hashable s2, Eq s1, Eq s2) => FSM s1 a -> FSM s2 a -> FSM (s1, s2) a
intersection (FSM (q1, sigma1, delta1, q0, f1)) (FSM (q2, sigma2, delta2, q0', f2)) = FSM (cartesianProduct q1 q2, sigma1, \(s1,s2)->(\a->(delta1 s1 a, delta2 s2 a)), (q0, q0'), cartesianProduct f1 f2)

--Operations on NDFSMs
concatLang::(Hashable s1, Hashable s2, Eq s1, Eq s2) => NDFSM s1 a -> NDFSM s2 a -> NDFSM (Either s1 s2) a
concatLang (NDFSM (q1, sigma1, delta1, q0, f1)) (NDFSM (q2, sigma2, delta2, q0', f2)) = NDFSM (q3, sigma1, delta3, Left q0, Set.map Right f2)
    where
        q3 = Set.map Left q1 `Set.union` Set.map Right q2
        delta3 (Left s) Nothing = Set.map Left (delta1 s Nothing) `Set.union` (if Set.member s f1 
                                     then Set.singleton (Right q0') --Add an epsilon transition from every final state to the start of the second machine
                                     else Set.empty)
        delta3 (Left s) a = Set.map Left (delta1 s a)
        delta3 (Right s) a = Set.map Right (delta2 s a)

kleene::(Hashable s, Eq s) => NDFSM s a -> NDFSM (Maybe s) a
kleene (NDFSM (q, sigma, delta, q0, f)) = NDFSM (Set.insert Nothing (Set.map Just q), sigma, delta', Nothing, Set.insert Nothing (Set.map Just f))
    where 
        delta' Nothing Nothing = Set.singleton (Just q0)
        delta' (Just s) Nothing = Set.map Just (delta s Nothing) `Set.union` (if Set.member s f
                                      then Set.singleton Nothing
                                      else Set.empty)
        delta' (Just s) a = Set.map Just (delta s a)

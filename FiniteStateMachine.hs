module FiniteStateMachine where

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import qualified Data.HashSet as Set
import Data.Foldable (Foldable, foldl)
import Prelude hiding (foldl)

--type State = Int
newtype FSM state alphabet = FSM (HashSet state, HashSet alphabet, state->alphabet->state, state, HashSet state)
--(Q, Sigma, delta, q0, F)
newtype NDFSM state alphabet = NDFSM (HashSet state, HashSet alphabet, state->Maybe alphabet->HashSet state, state, HashSet state) --Todo: Use some set not requirig Ord
--data FSM state alphabet = DSM () | NSM ()
states (FSM (q, sigma, delta, q0, f)) = q
alphabet (FSM (q, sigma, delta, q0, f)) = sigma
transition (FSM (q, sigma, delta, q0, f)) = delta
start (FSM (q, sigma, delta, q0, f)) = q0
acceptedStates (FSM (q, sigma, delta, q0, f)) = f

applyFSM :: (Hashable s, Eq s, Foldable f) => FSM s a -> f a -> Bool
applyFSM fsm str = foldl (transition fsm) (start fsm) str `Set.member` (acceptedStates fsm)


startND (NDFSM (q, sigma, delta, q0, f)) = q0
transitionND (NDFSM (q, sigma, delta, q0, f)) = delta
acceptedNDStates (NDFSM (q, sigma, delta, q0, f)) = f


applySingleEpsilonTransition::(Hashable s, Eq s) => HashSet s -> (s -> Maybe a -> HashSet s) -> HashSet s
applySingleEpsilonTransition set trans = set `setBind` (\e -> Set.insert e (flip trans Nothing e))
untilStableEpsilons::(Hashable s, Eq s) => HashSet s -> (s -> Maybe a -> HashSet s) -> HashSet s
untilStableEpsilons set trans = case takeWhile (uncurry (/=)) (zip transformations (tail transformations)) of
    [] -> set
    x -> snd . last $ x
    where
        transformations = iterate (flip applySingleEpsilonTransition trans) set

ndfsmToFSM :: (Hashable s, Eq s) => NDFSM s a -> FSM (HashSet s) a
ndfsmToFSM (NDFSM (q, sigma, delta, q0, f)) = FSM (newQ, sigma, newDelta, newq0, newf)
    where
        newQ = powerSet q
        newq0 = untilStableEpsilons (Set.singleton $ q0) (delta)
        newDelta stateSet a = stateSet `setBind` flip delta (Just a) `untilStableEpsilons` (delta)
        newf = Set.filter (not . null) $ Set.map (Set.intersection f) newQ -- set of all sets that contain an element of f.
        -- take all states, intersect each with F, take the ones that are not empty.

applyNDFSM :: (Hashable s, Eq s, Foldable f) => NDFSM s a -> f a -> Bool
applyNDFSM fsm str = any (flip Set.member (acceptedNDStates fsm)) allFinalStates
    where
        appliedInitialEpsilon = untilStableEpsilons (Set.singleton $ startND fsm) (transitionND fsm)
        allFinalStates = foldl (\acc e->(acc `setBind` flip (transitionND fsm) (Just e)) `untilStableEpsilons` (transitionND fsm)) appliedInitialEpsilon str

fsmToNDFSM :: (Hashable s, Eq s) => FSM s a -> NSFSM s a
fsmToNDFSM (FSM (q, sigma, delta, q0, f)) = NDFSM (q, sigma, delta', q0, f) where 
        delta' state alpha = case alpha of
            (Just a) -> Set.singleton (delta state a)
            Nothing -> Set.empty


powerSet :: (Hashable a, Eq a) => HashSet a -> HashSet (HashSet a)
powerSet mySet = Set.fromList $ map Set.fromList (powerSetList (Set.toList mySet))

powerSetList :: [a] -> [[a]]
powerSetList [] = [[]]
powerSetList (x:xs) = tailSet ++ map (x:) tailSet
    where tailSet = powerSetList xs

{- 
Theorem: Suppose we have an NDFSM m. If we construct m' by adding an epsilon transition that is a self-loop to every state,
    then the language described by m = the language described by m'

Proof: To be proved.
-}

setBind :: (Hashable s1, Hashable s2, Eq s1, Eq s2) => HashSet s1 -> (s1 -> HashSet s2) -> HashSet s2
setBind s f = foldl (Set.union) Set.empty $ Set.map f s

union::(Hashable s1, Hashable s2, Eq s1, Eq s2) => FSM s1 a -> FSM s2 a -> FSM (s1, s2) a
union (FSM (q1, sigma1, delta1, q0, f1)) (FSM (q2, sigma2, delta2, q0', f2)) = FSM (cross q1 q2, sigma1, \(s1,s2)->(\a->(delta1 s1 a, delta2 s2 a)), (q0, q0'), Set.union (cross f1 q2) (cross q1 f2))

intersection::(Hashable s1, Hashable s2, Eq s1, Eq s2) => FSM s1 a -> FSM s2 a -> FSM (s1, s2) a
intersection (FSM (q1, sigma1, delta1, q0, f1)) (FSM (q2, sigma2, delta2, q0', f2)) = FSM (cross q1 q2, sigma1, \(s1,s2)->(\a->(delta1 s1 a, delta2 s2 a)), (q0, q0'), cross f1 f2)

--unionND::(Hashable s1, Hashable s2, Eq s1, Eq s2) => NDFSM s1 a -> NDFSM s2 a -> NDFSM (s1, s2) a


cross::(Hashable a, Hashable b, Eq a, Eq b) => HashSet a -> HashSet b -> HashSet (a,b) --TODO: I can rewrite this without to/from list 
cross a b = Set.fromList $ (Set.toList a) >>= \x->(map (\y->(x,y)) (Set.toList b))

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
        
{-
cross'::(Hashable a, Hashable b, Eq a, Eq b) => HashSet a -> HashSet b -> HashSet (a,b)
cross' a b = foldl Set.union Set.empty doubleSet
    where
        disjointSum anElem s = Set.map (\a->(anElem, a)) s
        doubleSet = Set.map (flip disjointSum b) a
-}



newtype PDA state alphabet stack = PDA (HashSet state, HashSet alphabet, HashSet stack, state->Maybe alphabet->stack->(state, [stack]), state, HashSet state)


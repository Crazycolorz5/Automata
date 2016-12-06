import FiniteStateMachine as FSM

import Data.HashSet (HashSet)
import qualified Data.HashSet as Set


myAlphabet = Set.fromList [0,1] :: HashSet Int
myStates = Set.fromList [1..3] :: HashSet Int
delta (1, 0) = 2
delta (1, 1) = 1
delta (2, 0) = 3
delta (2, 1) = 1
delta (3, 0) = 3
delta (3, 1) = 3
myFSM = FSM (myStates, myAlphabet, curry delta, 1, Set.singleton 1)

myStates2 = Set.fromList [1..2] :: HashSet Int
delta2 (1, 0) = 1
delta2 (2, 0) = 2
delta2 (1, 1) = 2
delta2 (2, 1) = 1
myFSM2 = FSM (myStates2, myAlphabet, curry delta2, 1, Set.singleton 2)

myFSM3 = union myFSM myFSM2

myNDAlphabet = Set.fromList [0,1] :: HashSet Int
myNDStates = Set.fromList [1..5] :: HashSet Int

nddelta :: Int -> Maybe Int -> HashSet Int
nddelta 1 (Just 0) = Set.singleton 5
nddelta 1 (Nothing) = Set.singleton 2
nddelta 5 (Just 1) = Set.singleton 1
nddelta 2 (Just 0) = Set.singleton 3
nddelta 3 (Just 0) = Set.singleton 2
nddelta 2 (Just 1) = Set.singleton 4
nddelta 4 (Just 0) = Set.singleton 2
nddelta _ _ = Set.empty

myNDFSM = NDFSM (myNDStates, myNDAlphabet, nddelta, 1, Set.fromList [1, 2])


myNDStates2 = Set.fromList [1..7] :: HashSet Int
nddelta2 7 (Just 0) = Set.fromList [2,6]
nddelta2 1 Nothing = Set.fromList [4,7]
nddelta2 4 (Just 0) = Set.singleton 5
nddelta2 5 (Just 0) = Set.singleton 4
nddelta2 6 (Just 1) = Set.singleton 7
nddelta2 2 (Just 0) = Set.singleton 3
nddelta2 3 (Just 0) = Set.singleton 7
nddelta2 _ _ = Set.empty

myNDFSM2 = NDFSM (myNDStates2, myNDAlphabet, nddelta2, 1, Set.fromList [7, 4]) 

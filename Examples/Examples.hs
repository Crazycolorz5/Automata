import FiniteStateMachine as FSM
import PushdownAutomata as PDA
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


--PDA for a^nb^m | (a*) b^2n
myPDAStates = Set.fromList [0..4] :: HashSet Int
myPDAAlphabet = Set.fromList ['a', 'b'] :: HashSet Char
myPDAStackAlphabet = Set.singleton 'a' :: HashSet Char
pdaDelta 0 (Just 'a') Nothing = Set.singleton (0, Just 'a')
pdaDelta 0 Nothing Nothing = Set.fromList [(1, Nothing), (3, Nothing)]
pdaDelta 1 Nothing (Just 'a') = Set.singleton (1, Nothing)
pdaDelta 1 (Just 'b') Nothing = Set.singleton (2, Nothing)
pdaDelta 2 (Just 'b') Nothing = Set.singleton (1, Nothing)
pdaDelta 3 (Just 'b') (Just 'a') = Set.singleton (3, Nothing)
pdaDelta 3 Nothing Nothing = Set.singleton (4, Nothing)
pdaDelta _ _ _ = Set.empty
pdaFinalStates = Set.fromList [1, 4]

myPDA = PDA (myPDAStates, myPDAAlphabet, myPDAStackAlphabet, pdaDelta, 0, pdaFinalStates)

myCFG = pdaToCFG myPDA

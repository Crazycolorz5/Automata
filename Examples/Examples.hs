import FiniteStateMachine as FSM
import PushdownAutomata as PDA
import TuringMachine as TM
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set

assert p = if p then return () else error "Assertion failure."


--FSMs

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

myNDFSM = NDFSM (myNDStates, myNDAlphabet, nddelta, 1, Set.fromList [1, 2]) --(01)*(10 U 00)*


myNDStates2 = Set.fromList [1..7] :: HashSet Int
nddelta2 7 (Just 0) = Set.fromList [2,6]
nddelta2 1 Nothing = Set.fromList [4,7]
nddelta2 4 (Just 0) = Set.singleton 5
nddelta2 5 (Just 0) = Set.singleton 4
nddelta2 6 (Just 1) = Set.singleton 7
nddelta2 2 (Just 0) = Set.singleton 3
nddelta2 3 (Just 0) = Set.singleton 7
nddelta2 _ _ = Set.empty

myNDFSM2 = NDFSM (myNDStates2, myNDAlphabet, nddelta2, 1, Set.fromList [7, 4]) -- (00)* U (000 U 01)*

myFSM4 = ndfsmToFSM myNDFSM2


--PDAs

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

myPDA1 = PDA (myPDAStates, myPDAAlphabet, myPDAStackAlphabet, pdaDelta, 0, pdaFinalStates)
myPDAAccepts = cnfcfgProduces (cfgToCNFCFG . pdaToCFG $ myPDA1) 

myPDAStates2 = Set.singleton 0 :: HashSet Int
myPDAAlphabet2 = Set.fromList ['a', 'b'] :: HashSet Char
myPDAStackAlphabet2 = Set.empty :: HashSet Char
pdaDelta2 0 (Just 'a') Nothing = Set.singleton (0, Nothing)
pdaDelta2 _ _ _ = Set.empty
pdaFinalStates2 = Set.singleton 0
myPDA2 = PDA (myPDAStates2, myPDAAlphabet2, myPDAStackAlphabet2, pdaDelta2, 0, pdaFinalStates2) --Should recognize a*
aStar = cnfcfgProduces (cfgToCNFCFG . pdaToCFG $ myPDA2)

--We can now make such queries as
--myPDAAccepts ""
--myPDAAccepts "abb" (takes a LONG time)
--aStar "aaa"
--aStar "baa"

--a^n b^n | a* b^2n CFG:
-- S -> epsilon
-- S -> N
-- S -> M
-- N -> a N b | epsilon
-- M -> a M | M b b | epsilon
myCFGVars = Set.fromList ['S', 'N', 'M']
myCFGTerms = Set.fromList ['a', 'b']
myCFGRules = Set.fromList [Rule ('S', []), Rule ('S', [Left 'N']), Rule ('S', [Left 'M']), Rule ('N', [Right 'a', Left 'N', Right 'b']), Rule ('N', []), Rule ('M', [Right 'a', Left 'M']), Rule ('M', [Left 'M', Right 'b', Right 'b']), Rule ('M', [])]
myCFG = Grammar (myCFGVars, myCFGTerms, myCFGRules, 'S')
myCNF = cfgToCNFCFG myCFG

--Again, we can make queries like
--cnfcfgProduces myCNF "aaabb"






--TMs
myTMStates = Set.fromList [0..7] :: HashSet Int
myTMAlpha = Set.singleton '0' :: HashSet Char
myTMTape = Set.fromList ['0', 'X'] ::HashSet Char
myTMDelta :: Int -> Maybe Char -> (Int, Maybe Char, Direction)
myTMDelta 0 Nothing = (7, Nothing, R)
myTMDelta 0 (Just '0') = (1, Nothing, R)
myTMDelta 0 (Just 'X') = (0, Nothing, R)
myTMDelta 1 Nothing = (4, Nothing, L)
myTMDelta 1 (Just '0') = (2, Just '0', R)
myTMDelta 1 (Just 'X') = (1, Nothing, R)
myTMDelta 2 Nothing = (3, Nothing, L)
myTMDelta 2 (Just '0') = (5, Just '0', R)
myTMDelta 2 (Just 'X') = (2, Just 'X', R)
myTMDelta 3 Nothing = (4, Nothing, R)
myTMDelta 3 (Just '0') = (6, Just '0', L)
myTMDelta 3 (Just 'X') = (3, Just 'X', L)
myTMDelta 5 Nothing = (7, Nothing, L)
myTMDelta 5 (Just '0') = (2, Just 'X', R)
myTMDelta 5 (Just 'X') = (5, Just 'X', R)
myTMDelta 6 Nothing = (0, Nothing, R)
myTMDelta 6 (Just '0') = (6, Just '0', L)
myTMDelta 6 (Just 'X') = (6, Just 'X', L)
myTMDelta a b = error $  "Tried to delta " ++ show a ++ " and " ++ show b
myTM = TM (myTMStates, myTMAlpha, myTMTape, myTMDelta, 0, 7, 4)






main = do
    assert $ applyFSM myFSM [0,1,0,1]
    putStrLn "Passed test 1 (fsm true)."
    assert . not $ applyFSM myFSM [0,1,0,0,1]
    putStrLn "Passed test 2 (fsm false)."
    assert $ applyNDFSM myNDFSM [0,1,0,1,1,0,0,0]
    putStrLn "Passed test 3 (ndfsm true)."
    assert . not $ applyNDFSM myNDFSM [0,0,0]
    putStrLn "Passed test 4 (ndfsm false)."
    assert $ applyFSM myFSM4 [0,0,0,0]
    putStrLn "Passed test 5 (ndfsm to fsm true)."
    assert . not $ applyFSM myFSM4 [0,0,0,1]
    putStrLn "Passed test 6 (ndfsm to fsm false)."
    assert $ myPDAAccepts "" --Takes a long time
    putStrLn "Passed test 7 (pda true 1)."
    assert $ myPDAAccepts "ab" --Take a slightly less long time (don't have to regenerate CNFCFG)
    putStrLn "Passed test 8 (pda true 2)."
    assert . not $ myPDAAccepts "b"
    putStrLn "Passed test 9 (pda false)."
    let isPowerOfTwo x = if x == 0 then False else if x == 1 then True else (rem x 2 == 0) && isPowerOfTwo (div x 2)
        a = map (flip replicate '0') [0..100]
        tmRes = map (tmAccepts myTM) a
        haskRes = map (isPowerOfTwo . length) a
    assert $ tmRes == haskRes
    putStrLn "Passed test 10 (myTM holds for 0 to 100)."
    
    
{- Output:

*Main> :l Examples.hs
[1 of 5] Compiling TuringMachine    ( TuringMachine.hs, interpreted )
[2 of 5] Compiling SetTools         ( SetTools.hs, interpreted )
[3 of 5] Compiling PushdownAutomata ( PushdownAutomata.hs, interpreted )
[4 of 5] Compiling FiniteStateMachine ( FiniteStateMachine.hs, interpreted )
[5 of 5] Compiling Main             ( Examples.hs, interpreted )
Ok, modules loaded: FiniteStateMachine, PushdownAutomata, Main, SetTools, TuringMachine.
*Main> main
Passed test 1 (fsm true).
Passed test 2 (fsm false).
Passed test 3 (ndfsm true).
Passed test 4 (ndfsm false).
Passed test 5 (ndfsm to fsm true).
Passed test 6 (ndfsm to fsm false).
Passed test 7 (pda true 1).
Passed test 8 (pda true 2).
Passed test 9 (pda false).
Passed test 10 (myTM holds for 0 to 100).

-}

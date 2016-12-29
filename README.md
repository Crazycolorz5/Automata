# Automata
Emulating finite state machines, non-deterministic finite state machines, push-down automata, and 
turing machines, with mathematical rigor.

Since I use HashSets to represent the sets of states and symbols, the project is dependent on 
unordered-containers.

FiniteStateMachine.hs implements both deterministic and non-deterministic finite state machines. It 
then defines alorithms for converting between the two, and for a few language operations (such as 
intersection, union, kleene star).

PushdownAutomata.hs implements pushdown automata, context free grammars, and Chomsky normal form 
context free grammars (cnfcfg). The algorithm for checking if a PDA recognizes a string is converting 
the PDA to a CFG, then a cnfcfg, then generating all string 2n-1 generations away from the starting 
symbol, and checking if the string is on there. It's asymptotically exponential on 
the length of the string, with a base equal to the cube of the number of states, but it's provably 
terminating. I do not define any operations on languages (honestly, testing the 
code takes long enough as it is). 

TuringMachine.hs implements a turing machine type, and an algorithm for checking whether a turing 
machine accepts a string. Naturally, it may or may not terminate. Again, no other operations have been 
created. If you're interested in turing machines, check out the very simple implementation of 
Brain**** I created [here](https://github.com/Crazycolorz5/Brainhask).

Finally, the Examples folder contains Examples.hs, which creates examples of each of the kinds of 
machines, and has a main routine that verifies a few correct accept/reject decisions. There are also 
images for each machine constructed. 

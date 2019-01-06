New in version 2.4.5:

- Fixed a bug in algorithms/ParallelMinimization.java 
Preprocess_Buchi function that could cause false positives.
(know_inclusion_bw was sometimes called with an unsuitable
type of backward relation). 

New in version 2.4.4:

- Fixed a bug that could cause false negatives
when invoking RABIT without option -rd (or -fast).
- Added examples NFA_hard_1.ba, NFA_hard_2.ba
in the Examples subdirectory. These are NFA where inclusion
is hard to check (about 1h in RABIT; no success with other tools
like HKC and libvata).

New in version 2.4.3:

- Fixed a bug in algorithms/Minimization.java 
Preprocess_Buchi function that could cause false positives.
(know_inclusion_bw was sometimes called with an unsuitable
type of backward relation). 

New in version 2.4.2:

- Saturation method (options -sat and -sat2) has been slighly improved.
See example automaton Examples/fold.ba
- Bug fixed in random automata generation
- Added module algorithms/Determinization.java that implements the
powerset construction and NFA complementation.

New in version 2.4:

New option -sat that implements the transition saturation method
for automata reduction.
(-sat2 is a more aggressive version of -sat).
The deprecated option -add from version 2.3 has been removed.
The option -o allows to specify the output file name.


This bundle contains several tools.

1. RABIT version 2.4.5: 
A tool for checking language inclusion of nondeterministic Buchi automata (NBA)
and nondeterministic finite-word automata (NFA).

2. Reduce version 2.4.5:
A tool for minimizing nondeterministic Buchi automata (NBA) and 
nondeterministic finite-word automata (NFA).

3. TV:
An auxiliary tool for creating random automata according to the 
Tabakov-Vardi model.

4. toTimbuk:
This tool converts the .ba word-automata format into (a fragment of) the
.timbuk tree-automata format. 
The transformation does not exactly preserve the language
(the empty word is removed and a special accept action is appended at the end). 
However, language inclusion/equivalence between two so converted NFAs is preserved.
This fragment of the timbuk format is understood by other tools that handle
NFA (but not Buchi automata!) like
vata (http://www.fit.vutbr.cz/research/groups/verifit/tools/libvata/),
hkc (http://perso.ens-lyon.fr/damien.pous/hknt) and
limi (https://github.com/thorstent/Limi/)
The shells scripts hkcba.sh, vataba.sh and limiba.sh use these tools
to check inclusion between NFA in the .ba format.

For convenience, .jar files of the tools and some example automata are provided.
Each tool contains a help text on its use; just invoke them without arguments
for help.
The .ba file format of the files containing Buchi automata is 
documented at http://www.languageinclusion.org/doku.php?id=tools
This format is also supported by the GOAL tool 
(http://goal.im.ntu.edu.tw/wiki/doku.php?id=start)

The source code (Java >=7) is contained in the subdirectories
automata, comparator, datastructure, algorithms and mainfiles.
The code for the tools is located in the directory `mainfiles'.
(Set the classpath to the patent directory of these to compile). 

The subdirectory `Examples' contains more example automata.

The underlying theory is described in the paper
"Advanced Automata Minimization"
by R. Mayr and L. Clemente, that appeared in the POPL 2013 conference.
A longer technical report is available at 
http://homepages.inf.ed.ac.uk/rmayr/publications.html
http://arxiv.org/abs/1210.6624
A forthcoming journal paper additionally explains the saturation method.
See also www.languageinclusion.org

Examples of how to use the tools:

java -jar Reduce.jar fischer.3.2.c.ba 10
(This reduces the Buchi automaton fischer.3.2.c.ba with a method using
lookahead 10.)

java -jar Reduce.jar fischer.3.2.c.ba 10 -sat
(This reduces the Buchi automaton fischer.3.2.c.ba with a method using
lookahead 10, and possibly adding transitions. In this case it yields a smaller 
automaton than the standard method.)

java -jar Reduce.jar fischer.3.2.c.ba 10 -finite
(This reduces the NFA fischer.3.2.c.ba with a method using
lookahead 10.)

java -jar Reduce.jar fischer.3.2.c.ba 10 -finite -sat
(This reduces the NFA fischer.3.2.c.ba with a method using
lookahead 10, and possibly adding transitions.)

java -jar RABIT.jar fischer.3.c.ba fischer.3.2.c.ba -fast
(This checks language inclusion of the Buchi automata 
fischer.3.c.ba and fischer.3.2.c.ba by using the fastest method
available in the RABIT tool.)

java -jar RABIT.jar fischer.3.2.c.ba fischer.3.c.ba -fastc
(This checks language inclusion of the Buchi automata 
fischer.3.2.c.ba and fischer.3.c.ba by using the fastest method
available in the RABIT tool and reports a counterexample.)


java -jar RABIT.jar finite_reduced_10_fischer.3.2.c.ba fischer.3.2.c.ba -fast -finite
(This checks language inclusion of the NFAs
finite_reduced_10_fischer.3.2.c.ba (created by the Reduce-minimization command
above) and fischer.3.2.c.ba, by using the fastest method for NFA inclusion
available in the RABIT tool.)

java -jar TV.jar 300 1.8 0.5 test
java -jar Reduce.jar test.ba 10
(This creates a Tabakov-Vardi random automaton test.ba with 300 states, 
alphabet size 2, transition density 1.8 and acceptance density 0.5.
This is then reduced (as a Buchi automaton) with a method using lookahead 10.)


Note on the Reduce tool:

This current version 2.4. of Reduce implements the Light-k and Heavy-k methods
described in the POPL 2013 paper, plus some additional methods (e.g., -sat).
To get Light-k: Invoke with option -light
To get Heavy-k: Invoke with option -nojump
To get the (better) default: Invoke without options.
Invoking with option -pebble uses a method with 2-pebble
simulation in some limited circumstances. 
Theoretically this reduces better, but in practice it is slow
and mostly not worth the effort.
With option -sat it might create an automaton with fewer states but possibly
more transitions.
The options -light, -nojump, -pebble, -sat are mutually exclusive.

By default, Reduce reduces Buchi automata. 
One can switch the semantics to NFA by using the additional option -finite

As usual, the option -par causes some operations to be computed in parallel
to make it faster. Performance improvements vary.

All experiments described in the POPL 2013 paper referring to
the Heavy-k method used the option -nojump.

Attribution: 

This code of the RABIT 2.4 and Reduce 2.4 tools 
is developed and maintained by Richard Mayr 
and licensed under GPLv2.
It re-uses some parts of the code of the old version
1.1 of the RABIT-tool, developed by Y.F. Chen, C. Hong,
and R. Mayr.

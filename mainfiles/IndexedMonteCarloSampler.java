/* Written by Yong Li                                                     */
/* Copyright (c) 2018                                                     */
/*                                                                        */
/* This program is free software; you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation; either version 2 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* You should have received a copy of the GNU General Public License      */
/* along with this program; if not, write to the Free Software            */
/* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA*/

package mainfiles;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ThreadLocalRandom;

import algorithms.Options;
import gnu.trove.map.TIntIntMap;
import gnu.trove.map.hash.TIntIntHashMap;
import oracle.EmptinessCheck;
import oracle.Membership;
import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.Pair;

/**
 * Radu Grosu and Scott A.Smolka. 
 *  Monte Carlo Model checking
 *  
 *  We improved the sampling algorithm for inclusion checking
 */
public class IndexedMonteCarloSampler {

    private IndexedMonteCarloSampler() {

    }

    private static Pair<String, FAState> rNext(FiniteAutomaton automaton, FAState s) {
        // uniformly pick the successor
        List<Pair<String, FAState>> nexts = new ArrayList<>();
        for (String symb : automaton.alphabet) {
            Set<FAState> succs = s.getNext(symb);
            if (succs == null)
                continue;
            for (FAState succ : succs) {
                nexts.add(new Pair<>(symb, succ));
            }
        }
        // pick a state randomly
        int sNr = ThreadLocalRandom.current().nextInt(0, nexts.size());
        assert sNr < nexts.size();
        return nexts.get(sNr);
    }

    public static boolean removeDeadStates(FiniteAutomaton automaton) {
        // preprocessing, make sure every state in automaton has successors
        Set<FAState> states = new TreeSet<>();
        states.addAll(automaton.states);
        while (true) {
            boolean changed = false;
            Set<FAState> temp = new TreeSet<>();
            for (FAState st : states) {
                if (st.getNext().isEmpty()) {
                    automaton.removeState(st);
                    temp.add(st);
                    changed = true;
                }
            }
            if (!changed)
                break;
            else {
                states.removeAll(temp);
            }
        }
        states = null;
        if (automaton.F.isEmpty())
            return true;
        // start sampling
        FAState s = automaton.getInitialState();
        if (s.getNext().isEmpty())
            return true;
        return false;
    }
    
 // only for 1 and 2, only allowed three apearacnces for one state
    private static boolean terminate(int index, int K) {
        if(index >= K) return true;
        // the probability whether to stop right now or not
        int sNr = ThreadLocalRandom.current().nextInt(0, 2);
        return sNr == 1;
    }

    /**
     * Indexed Monte Carlo
     * Make sure that every state has at least one successor
     */
    public static Pair<Pair<List<String>, List<String>>, Boolean> getRandomLasso(FiniteAutomaton automaton, int K) {

        // start sampling
        FAState s = automaton.getInitialState();
        int i = 0, f = -1;
        TIntIntMap hTable = new TIntIntHashMap();
        TIntIntMap cTable = new TIntIntHashMap();
        List<String> wList = new ArrayList<>();
        while (true) {
            boolean occurred = hTable.containsKey(s.id);
            if(occurred) {
                assert cTable.containsKey(s.id);
                int index = cTable.get(s.id);
                if(terminate(index, K)) {
                    break;
                }else {
                    index ++;
                    cTable.put(s.id, index);
                }
            }else {
                // next time, it should be one
                cTable.put(s.id, 1);
            }
            hTable.put(s.id, i);
            if (automaton.F.contains(s)) {
                f = i;
            }
            Pair<String, FAState> pair = rNext(automaton, s);
            wList.add(pair.getLeft());
            s = pair.getRight();
            ++i;
        }

        List<String> prefix = new ArrayList<>();
        List<String> suffix = new ArrayList<>();
        int start = hTable.get(s.id); // the state repeat
        for (int j = 0; j < start; j++) {
            prefix.add(wList.get(j));
        }
        for (int j = start; j < wList.size(); j++) {
            suffix.add(wList.get(j));
        }
        boolean accept;
        if (hTable.get(s.id) <= f) {
            accept = true;
        } else {
            accept = false;
        }
        return new Pair<>(new Pair<>(prefix, suffix), accept);
    }

    private static void test() {
        FiniteAutomaton aut = new FiniteAutomaton();
        FAState s1 = aut.createState();
        FAState s2 = aut.createState();
        FAState s3 = aut.createState();
        FAState s4 = aut.createState();

        aut.setInitialState(s1);
        aut.addTransition(s1, s1, "a");
        aut.addTransition(s1, s2, "b");
        aut.addTransition(s2, s3, "c");
        aut.addTransition(s2, s4, "b");
        aut.addTransition(s3, s1, "a");
        aut.addTransition(s3, s4, "b");
        aut.addTransition(s4, s4, "c");

        aut.F.add(s3);

        double epsilon = 1.8e-3, delta = 0.1;
        long num = getMSamples(epsilon, delta);
        System.out.println("num=" + num);
        for (int n = 0; n < num; n++) {
            Pair<Pair<List<String>, List<String>>, Boolean> result = getRandomLasso(aut, 2);
            System.out.println("prefix: " + result.getLeft().getLeft());
            System.out.println("suffix: " + result.getLeft().getRight());
            System.out.println("membership: " + result.getRight());
            if (result.getRight()) {
                break;
            }
        }
    }

    private static void test1() {
        FiniteAutomaton aut = new FiniteAutomaton("/home/liyong/Downloads/RABIT243/Examples/bug.ba");
//        AutomatonPrinter.print(aut, System.out);

        double epsilon = 1.8e-3, delta = 0.1;
        long num = getMSamples(epsilon, delta);
        System.out.println("num=" + num);
        for (int n = 0; n < num; n++) {
            Pair<Pair<List<String>, List<String>>, Boolean> result = getRandomLasso(aut, 2);
            if (result == null)
                return;
            Pair<List<String>, List<String>> pair = result.getLeft();
            boolean acc = isAccepting(aut, pair.getLeft(), pair.getRight());
            if (result.getRight().booleanValue() != acc) {
                System.out.println("prefix: " + pair.getLeft());
                System.out.println("suffix: " + pair.getRight());
                System.out.println("membership: " + result.getRight());
                System.exit(0);
            }
        }
    }
    
    private static boolean isAccepting(FiniteAutomaton aut
            , List<String> prefix, List<String> suffix) {
        Membership checker = new Membership(aut);
        return checker.checkMembership(prefix, suffix);
    }

    public static Boolean process(FiniteAutomaton aut1, FiniteAutomaton aut2) {

        boolean isEmpty1 = removeDeadStates(aut1);
        if (isEmpty1) {
            System.out.println("Included (already proven during dead states removal");
            return true;
        }
        boolean isEmpty2 = removeDeadStates(aut2);
        if (isEmpty2 && !isEmpty1) {
            EmptinessCheck checker = new EmptinessCheck(aut1);
            boolean empty = checker.isEmpty();
            if (!empty) {
                checker.findpath();
                System.out.println("Not included (already proven during states removal");
                if(Options.verbose) System.out.println("Counterexample: "+ checker.getInifinteWord().getLeft()+" ("+checker.getInifinteWord().getRight()+")");
                return false;
            }
        }
        System.out.println("Aut A (after processing) : # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
        System.out.println("Aut B (after processing) : # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
        System.out.println("Start to prove inclusion via sampling...");
        long time = System.currentTimeMillis();
        double epsilon = 0.0018;
        double delta = 0.001;
        int K = aut2.states.size() + aut1.states.size();
        long num = getMSamples(epsilon, delta);
        System.out.println("Trying " + num + " samples from A automaton...");
        for (int i = 0; i < num; i++) {
            Pair<Pair<List<String>, List<String>>, Boolean> result = getRandomLasso(aut1, K);
            Pair<List<String>, List<String>> word = result.getLeft();
            boolean needCheck = false;
            if (result.getRight()) {
                needCheck = true;
            } else {
                needCheck = isAccepting(aut1, word.getLeft(), word.getRight());
            }
            if (needCheck) {
                boolean acc = isAccepting(aut2, word.getLeft(), word.getRight());
                if (!acc) {
                    System.out.println("Not included (already proven during sampling");
                    if(Options.verbose) System.out.println("Counterexample: "+ result.getLeft().getLeft()+" ("+result.getLeft().getRight()+")");
                    time = System.currentTimeMillis() - time;
                    System.out.println("Samping time used(ms): " + time);
                    return false;
                }
            }
        }
//        if(args.length <= 4) {
//            K = aut1.states.size();
//        }
        System.out.println("Trying " + num + " samples from B automaton...");
        for (int i = 0; i < num; i++) {
            Pair<Pair<List<String>, List<String>>, Boolean> result = getRandomLasso(aut2, K);
            Pair<List<String>, List<String>> word = result.getLeft();
            boolean needCheck = false;
            if (result.getRight()) {
                needCheck = false; // in aut2, no need
            } else {
                needCheck = ! isAccepting(aut2, word.getLeft(), word.getRight());
            }
            if (needCheck) {
                boolean acc = isAccepting(aut1, result.getLeft().getLeft(), result.getLeft().getRight());
                if (acc) {
                    System.out.println("Not included (already proven during sampling");
                    if(Options.verbose) System.out.println("Counterexample: "+ result.getLeft().getLeft()+" ("+result.getLeft().getRight()+")");
                    time = System.currentTimeMillis() - time;
                    System.out.println("Samping time used(ms): " + time);
                }
            }
        }
        time = System.currentTimeMillis() - time;
        System.out.println("Samping time used(ms): " + time);
        return null;
    }

    public static long getMSamples(double epsilon, double delta) {
        double result = Math.log(delta) / (1.0 * Math.log(1 - epsilon));
        long num = Math.round(result);
        return num;
    }

}

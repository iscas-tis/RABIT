/* Written by Yu-Fang Chen, Richard Mayr, and Chih-Duo Hong               */
/* Copyright (c) 2010-2012                  	                                  */
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

import java.lang.management.*;
import java.lang.Exception;

import java.util.Random;
import java.util.TreeMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;
import datastructure.Pair;

/*
import java.util.Arrays;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
*/

import automata.FAState;
import automata.FiniteAutomaton;
import automata.AutomatonPreprocessingResult;

import algorithms.InclusionAnti;
import algorithms.InclusionOpt;
import algorithms.InclusionOptBVLayered;
import algorithms.Options;
import algorithms.Minimization;
import algorithms.Simulation;
import algorithms.ParallelMinimization;
import algorithms.ParallelSimulation;


/**
 * 
 * @author Richard Mayr, Yu-Fang Chen
 *  changed by Yong Li 
 */
public class RABIT {
    static long timeout=0;
    static boolean timeout_set=false;

	// Transform finite automata into BA s.t. language inclusion is preserved.
		private static FiniteAutomaton toBA(FiniteAutomaton aut){
		if(aut.alphabet.contains("_specialaction359_")){
			System.out.println("Error: Alphabet name clash. Exiting.");
			System.exit(0);
		    }
		FAState acc = aut.createState();
		Iterator<FAState> it=aut.F.iterator();
		while(it.hasNext()){
		    FAState state=it.next();
		    aut.addTransition(state, acc, "_specialaction359_");
		}
		aut.addTransition(acc, acc, "_specialaction359_");
		aut.F.clear();
		aut.F.add(acc);
		return aut;
	    }

 
    private static int bfs_depth(FiniteAutomaton aut1, FiniteAutomaton aut2){
	int s = Math.max(aut1.alphabet.size(),aut2.alphabet.size());
	if(s <= 2) return 8;
	else if(s==3) return 5;
	else if(s==4) return 4;
	else if(s==5) return 4;
	else if(s==6) return 3;
	else if(s <= 20) return 2;
	else return 1;
    }


    private static boolean inclusion_Buchi(FiniteAutomaton aut1, FiniteAutomaton aut2){
        // --------------- LY added ---------------
        // we can also do sampling before minimization
        if(Options.sampling) {
            // do Monte Carlo sampling for inclusion checking
            Boolean result = IndexedMonteCarloSampler.process(aut1, aut2);
            if(result != null) {
                return result;
            }
        }
        // --------------- LY added ---------------
		    Minimization Minimizer = new Minimization();
			// First do a lightweight preprocessing
			AutomatonPreprocessingResult x = Minimizer.Lightweight_Preprocess_Buchi(aut1, aut2);
			aut1=x.system;
			aut2=x.spec;
			if(Options.verbose){
			    System.out.println("Aut A (after light preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			    System.out.println("Aut B (after light preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
			}
			if(x.result){
			    if(Options.verbose) System.out.println("Included (already proven during lightweight preprocessing).");
			    return true;
			}

			// Try a short BFS, hoping for a short counterexample.
			// This is only correct of the automata have NO dead states.
			if(Options.rd){
			    int depth = bfs_depth(aut1, aut2);
			    if(Options.verbose) System.out.println("Try BFS search up to depth "+depth+" for a short counterexample.");
			    Simulation sim = new Simulation();
			
			    String d = sim.BFS_Compare(aut1, aut2, depth);
			    if(d != null){
				if(Options.verbose) System.out.println("Counterexample: "+d);
				return false;
			    }
			    else if(Options.verbose){
				if(Options.verbose) System.out.println("BFS depth "+depth+" did not find a counterexample.");
			    }
			}
			
		    // Now, if the automata are not too large, 
		    // try a short run of the Ramsey algorithm (<= 50 metagraphs), in the hope of solving the problem without heavy preprocessing
			if(aut1.states.size()+aut2.states.size() <= 400){
			    if(Options.verbose) System.out.println("Trying Ramsey method with small bound (50 metagraphs).");
			    
			    InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1,aut2,50);
			    inclusion.run();
			    if(!inclusion.timeout){
				if(Options.verbose) System.out.println("Solved. Metagraphs added to the Next set: "+inclusion.mggen);
				if(inclusion.isIncluded()) return true; else {
				    if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix+" ("+inclusion.counterexample_loop+")");
				    return false;
				}
			    }
			    else if(Options.verbose) System.out.println("Light methods alone could not solve it. Trying heavy preprocessing.");
			}
			else if(Options.verbose) System.out.println("Automata still too large. Trying heavy preprocessing.");
			
			// Now do the heavy preprocessing (and later possibly full Ramsey).
			x = Minimizer.Preprocess_Buchi(aut1, aut2);
			aut1=x.system;
			aut2=x.spec;
			if(Options.verbose){
			    System.out.println("Aut A after minimization: # of Trans. "+ aut1.trans + ", # of States " + aut1.states.size()+".");
			    System.out.println("Aut B after minimization: # of Trans. "+ aut2.trans + ", # of States " + aut2.states.size()+".");
			}
			if(x.result){
			    if(Options.verbose) System.out.println("Included (already proven during preprocessing)");
			    return true;
			}
			else{
			    Options.globalstop=false;
			    FairsimThread fst=null;
			    if(Options.jumping_fairsim){
				fst = new FairsimThread(aut1, aut2);
				fst.start();
			    }
			    // Start Ramsey procedure with limit==0, which means no limit.
			    InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1,aut2,0);
			    inclusion.run();
			    if(Options.jumping_fairsim) fst.stop();
			    if(Options.verbose) System.out.println("Metagraphs added to the Next set: "+inclusion.mggen);
			    if(inclusion.isIncluded()) return true; else {
				if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix+" ("+inclusion.counterexample_loop+")");
				return false;
			    }
			}
    }



    private static boolean par_inclusion_Buchi(FiniteAutomaton aut1, FiniteAutomaton aut2){
		    ParallelMinimization Minimizer = new ParallelMinimization();
			// First do a lightweight preprocessing
			AutomatonPreprocessingResult x = Minimizer.Lightweight_Preprocess_Buchi(aut1, aut2);
			aut1=x.system;
			aut2=x.spec;
			if(Options.verbose){
			    System.out.println("Aut A (after light preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			    System.out.println("Aut B (after light preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
			}
			if(x.result){
			    if(Options.verbose) System.out.println("Included (already proven during lightweight preprocessing).");
			    return true;
			}

			// Try a short BFS, hoping for a short counterexample.
			// This is only correct of the automata have NO dead states.
			if(Options.rd){
			    int depth = bfs_depth(aut1, aut2);
			    if(Options.verbose) System.out.println("Try BFS search up to depth "+depth+" for a short counterexample.");
			    Simulation sim = new Simulation();
			    String d = sim.BFS_Compare(aut1, aut2, depth);
			    if(d != null){
				if(Options.verbose) System.out.println("Counterexample: "+d);
				return false;
			    }
			    else if(Options.verbose){
				if(Options.verbose) System.out.println("BFS depth "+depth+" did not find a counterexample.");
			    }
			}
			
		    // Now, if the automata are not too large, 
		    // try a short run of the Ramsey algorithm (<= 50 metagraphs), in the hope of solving the problem without heavy preprocessing
			if(aut1.states.size()+aut2.states.size() <= 400){
			    if(Options.verbose) System.out.println("Trying Ramsey method with small bound (50 metagraphs).");
			    
			    InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1,aut2,50);
			    inclusion.run();
			    if(!inclusion.timeout){
				if(Options.verbose) System.out.println("Solved. Metagraphs added to the Next set: "+inclusion.mggen);
				if(inclusion.isIncluded()) return true; else {
				    if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix+" ("+inclusion.counterexample_loop+")");
				    return false;
				}
			    }
			    else if(Options.verbose) System.out.println("Light methods alone could not solve it. Trying heavy preprocessing.");
			}
			else if(Options.verbose) System.out.println("Automata still too large. Trying heavy preprocessing.");
			
			// Now do the heavy preprocessing (and later possibly full Ramsey).
			x = Minimizer.Preprocess_Buchi(aut1, aut2);
			aut1=x.system;
			aut2=x.spec;
			if(Options.verbose){
			    System.out.println("Aut A after minimization: # of Trans. "+ aut1.trans + ", # of States " + aut1.states.size()+".");
			    System.out.println("Aut B after minimization: # of Trans. "+ aut2.trans + ", # of States " + aut2.states.size()+".");
			}
			if(x.result){
			    if(Options.verbose) System.out.println("Included (already proven during preprocessing)");
			    return true;
			}
			else{
			    Options.globalstop=false;
			    FairsimThread fst=null;
			    if(Options.jumping_fairsim){
				fst = new FairsimThread(aut1, aut2);
				fst.start();
			    }
			    // Start Ramsey procedure with limit==0, which means no limit.
			    InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1,aut2,0);
			    inclusion.run();
			    if(Options.jumping_fairsim) fst.stop();
			    if(Options.verbose) System.out.println("Metagraphs added to the Next set: "+inclusion.mggen);
			    if(inclusion.isIncluded()) return true; else {
				if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix+" ("+inclusion.counterexample_loop+")");
				return false;
			    }
			}
    }




    private static boolean inclusion_finite(FiniteAutomaton aut1, FiniteAutomaton aut2){
		    if(aut1.F.contains(aut1.getInitialState()) && !aut2.F.contains(aut2.getInitialState())){
			if(Options.verbose) System.out.println("Not included. (Empty word in A, but not in B.)");
			return false;
		    }
		    Minimization Minimizer = new Minimization();
		    aut1 = Minimizer.finite_removeDead(aut1);
		    aut2 = Minimizer.finite_removeDead(aut2);
		    // The FiniteOneAcc ensures only one absorbing accepting state, but removes the empty word from the lang.
	            aut1 = Minimizer.FiniteOneAcc(aut1);
		    aut2 = Minimizer.FiniteOneAcc(aut2);
		    if(Options.verbose){
			System.out.println("Removed dead states and transformed into a form with just one accepting state.");
			System.out.println("Aut A (after this transformation): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			System.out.println("Aut B (after this transformation): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
		    }
		    AutomatonPreprocessingResult x = Minimizer.Lightweight_Preprocess_Finite(aut1, aut2);
		    if(x.result){
			if(Options.verbose) System.out.println("Included (already proven during lightweight finite-aut. preprocessing).");
			return true;
		    }
		    aut1=x.system;
		    aut2=x.spec;
		    if(Options.verbose){
			    System.out.println("Aut A (after finite aut. light preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			    System.out.println("Aut B (after finite aut. light preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
		    }

		    // The following test is only correct, because the automata have no dead states.
		    int depth = bfs_depth(aut1, aut2);
		    if(Options.verbose) System.out.println("Trying to find a short (up-to depth "+depth+") counterexample.");
		    Simulation sim = new Simulation();
		    
		    String d = sim.acc_BFS_Compare(aut1, aut2, depth);
		    if(d != null){
			if(Options.verbose) System.out.println("Counterexample: "+d);
			return false;
		    }
		    else if(Options.verbose){
			    System.out.println("BFS depth "+depth+" did not find a counterexample.");
		    }

		    x = Minimizer.Preprocess_Finite(aut1, aut2);
		    if(x.result){
			if(Options.verbose) System.out.println("Included (already proven during finite-aut. preprocessing).");
			return true;
		    }

		    aut1=x.system;
		    aut2=x.spec;
		    if(Options.verbose){
			    System.out.println("Aut A (after full preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			    System.out.println("Aut B (after full preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
			    System.out.println("Translating to Buchi inclusion and searching for a counterexample.");
		    }
		    // Starting simulation in separate thread
			Options.globalstop=false;
			DirectsimThread fst=null;
			if(Options.jumping_fairsim){
			    if(Options.verbose) System.out.println("Trying to establish inclusion by simulation in parallel.");
			    fst = new DirectsimThread(aut1, aut2);
			    fst.start();
			}
		    FiniteAutomaton aut1x = Minimizer.finite_removeDead(aut1);
		    FiniteAutomaton aut2x = Minimizer.finite_removeDead(aut2);
		    aut1x=toBA(aut1x);
		    aut2x=toBA(aut2x);

 			InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1x,aut2x,0);
			inclusion.run();
			if(Options.verbose)  System.out.println("Metagraphs added to the Next set "+inclusion.mggen);
			if(Options.jumping_fairsim) fst.stop();
			if(inclusion.isIncluded()) return true; else {
				if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix);
				return false;
			    }
    }



    private static boolean par_inclusion_finite(FiniteAutomaton aut1, FiniteAutomaton aut2){
		    if(aut1.F.contains(aut1.getInitialState()) && !aut2.F.contains(aut2.getInitialState())){
			if(Options.verbose) System.out.println("Not included. (Empty word in A, but not in B.)");
			return false;
		    }
		    ParallelMinimization Minimizer = new ParallelMinimization();
		    aut1 = Minimizer.finite_removeDead(aut1);
		    aut2 = Minimizer.finite_removeDead(aut2);
		    // The FiniteOneAcc ensures only one absorbing accepting state, but removes the empty word from the lang.
	            aut1 = Minimizer.FiniteOneAcc(aut1);
		    aut2 = Minimizer.FiniteOneAcc(aut2);
		    if(Options.verbose){
			System.out.println("Removed dead states and transformed into a form with just one accepting state.");
			System.out.println("Aut A (after this transformation): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			System.out.println("Aut B (after this transformation): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
		    }
		    AutomatonPreprocessingResult x = Minimizer.Lightweight_Preprocess_Finite(aut1, aut2);
		    if(x.result){
			if(Options.verbose) System.out.println("Included (already proven during lightweight finite-aut. preprocessing).");
			return true;
		    }
		    aut1=x.system;
		    aut2=x.spec;
		    if(Options.verbose){
			    System.out.println("Aut A (after finite aut. light preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			    System.out.println("Aut B (after finite aut. light preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
		    }

		    // The following test is only correct, because the automata have no dead states.
		    int depth = bfs_depth(aut1, aut2);
		    if(Options.verbose) System.out.println("Trying to find a short (up-to depth "+depth+") counterexample.");
		    Simulation sim = new Simulation();
		    String d = sim.acc_BFS_Compare(aut1, aut2, depth);
		    if(d != null){
			if(Options.verbose) System.out.println("Counterexample: "+d);
			return false;
		    }
		    else if(Options.verbose){
			    System.out.println("BFS depth "+depth+" did not find a counterexample.");
		    }

		    x = Minimizer.Preprocess_Finite(aut1, aut2);
		    if(x.result){
			if(Options.verbose) System.out.println("Included (already proven during finite-aut. preprocessing).");
			return true;
		    }

		    aut1=x.system;
		    aut2=x.spec;
		    if(Options.verbose){
			    System.out.println("Aut A (after full preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
			    System.out.println("Aut B (after full preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
			    System.out.println("Translating to Buchi inclusion and searching for a counterexample.");
		    }
		    // Starting simulation in separate thread
			Options.globalstop=false;
			DirectsimThread fst=null;
			if(Options.jumping_fairsim){
			    if(Options.verbose) System.out.println("Trying to establish inclusion by simulation in parallel.");
			    fst = new DirectsimThread(aut1, aut2);
			    fst.start();
			}
		    FiniteAutomaton aut1x = Minimizer.finite_removeDead(aut1);
		    FiniteAutomaton aut2x = Minimizer.finite_removeDead(aut2);
		    aut1x=toBA(aut1x);
		    aut2x=toBA(aut2x);

 			InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1x,aut2x,0);
			inclusion.run();
			if(Options.verbose)  System.out.println("Metagraphs added to the Next set "+inclusion.mggen);
			if(Options.jumping_fairsim) fst.stop();
			if(inclusion.isIncluded()) return true; else {
				if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix);
				return false;
			    }
    }




        static class FairsimThread extends Thread {
	    FiniteAutomaton system;
	    FiniteAutomaton spec;
	    Minimization min2 = new Minimization();
	    FairsimThread(FiniteAutomaton aut1, FiniteAutomaton aut2) {
	     this.system = min2.Buchi_decompose_selfloops(aut1);
	     this.spec = aut2;
	    }

	    public void run() {
		Simulation sim = new Simulation();
		
		int la=1;

		if(Options.jumping_fairsim_extra){
		while(true){
		    if((la % 2)==1){
			if(Options.verbose) System.out.println("Computing X_C_jumping fair sim with la: "+la);
			if(sim.x_JumpingBLAFairSimRelNBW(system, spec, la, 2)){
			    if(Options.verbose) System.out.println("X_C_Jumping fairsim proved inclusion first at lookahead "+la+".");
			    Options.globalstop=true;
			    return;
			}
		    }
		    else{
			if(Options.verbose) System.out.println("Computing X Segment_jumping fair sim with la: "+la);
			if(sim.x_JumpingBLAFairSimRelNBW(system, spec, la, 3)){
			    if(Options.verbose) System.out.println("X Segment_Jumping fairsim proved inclusion first at lookahead "+la+".");
			    Options.globalstop=true;
			    return;
			}
		    }
		la++;
		}
		}
		else{
		while(true){
		    if((la % 2)==1){
			if(Options.verbose) System.out.println("Computing C_jumping fair sim with la: "+la);
			if(sim.JumpingBLAFairSimRelNBW(system, spec, la, 2)){
			    if(Options.verbose) System.out.println("C_Jumping fairsim proved inclusion first at lookahead "+la+".");
			    Options.globalstop=true;
			    return;
			}
		    }
		    else{
			if(Options.verbose) System.out.println("Computing Segment_jumping fair sim with la: "+la);
			if(sim.JumpingBLAFairSimRelNBW(system, spec, la, 3)){
			    if(Options.verbose) System.out.println("Segment_Jumping fairsim proved inclusion first at lookahead "+la+".");
			    Options.globalstop=true;
			    return;
			}
		    }
		la++;
		}
		}
	    }
	}



        static class DirectsimThread extends Thread {
	    FiniteAutomaton system;
	    FiniteAutomaton spec;
	    DirectsimThread(FiniteAutomaton aut1, FiniteAutomaton aut2) {
             this.system = aut1;
	     this.spec = aut2;
	    }

	    public void run() {
		Simulation sim = new Simulation();
		Minimization min = new Minimization();
		int la=1;
		Set<Pair<FAState, FAState>> rel;

		while(true){
		    if(Options.verbose) System.out.println("Computing lookahead direct sim with la: "+la);
			rel = sim.BLASimRelNBW(system, spec, la);
			if(min.know_inclusion(system, spec, rel)){
			    if(Options.verbose) System.out.println("Lookahead sim proved inclusion first at lookahead "+la+".");
			    Options.globalstop=true;
			    return;
			}
		la++;
		}
	    }
	}



    public static void main(String[] args) {
		boolean antichain=false;

		for(int i=0;i<args.length;i++){
			if(args[i].compareTo("-h")==0){
			    System.out.println("RABIT v2.4.4 (Lookahead-simulation and Ramsey-based automata inclusion testing for Buchi automata (default) and NFA (with option -finite)).");
				System.out.println("Usage: java -jar RABIT.jar aut1.BA aut2.BA [-h -v -q -qr -c -rd -DFS -SFS -fplus -b -d -eb -cpt -sp -de -blamin -blasub -blaoffset n -blafixed n -tp -jq -jf -jf2 -fast -fastc] [-finite|-finite2] [-par]");

				System.out.println("Recommended use: java -jar RABIT.jar aut1.BA aut2.BA -fast");
				System.out.println("             or: java -jar RABIT.jar aut1.BA aut2.BA -fast -jf");
				System.out.println("For NFA        : java -jar RABIT.jar aut1.BA aut2.BA -fast -finite");
				System.out.println("\nOptions:");
				System.out.println("-h: Show this page");
				System.out.println("-v: Verbose mode");
				System.out.println("-v2: Very verbose mode");
				System.out.println("-q: Do quotienting w.r.t. forward simulation");
				System.out.println("-qr: Do fw/bw quotienting and removal of useless transitions repeatedly until a fixed point is reached. Overrides -q");
				System.out.println("-c: Use forward simulation between aut1 and aut2");
				System.out.println("-rd: Remove dead states");
				System.out.println("-DFS: Use DFS searching strategy (default: BFS strategy)");
				System.out.println("-SFS: Use smallest-first searching strategy (default: BFS strategy)");
				System.out.println("-fplus: Use one-step-further forward simulation");
				System.out.println("-b: Use backward simulation");
				System.out.println("-d: Debug mode");
				System.out.println("-eb: Earlier detection of counterexamples (with minimal overhead)");
				System.out.println("-cpt: Do a cheap pretest before subsumption checking.");
				System.out.println("-sp: Apply more extensive automata minimization and preprocessing. Only effective when used together with options -b -qr -rd.");
				System.out.println("-de: Use delayed simulation. Overrides -q.");
				System.out.println("-blamin: Use lookahead simulation in minimization.");
				System.out.println("-blasub: Use lookahead simulation for subsumption.");
				System.out.println("-blafixed n: Specify fixed lookahead n>=1. Overrides the automatic.");
				System.out.println("-blaoffset n: Increase automatic lookahead by integer n (can be negative)");
				System.out.println("-tp: Pruning of little brothers of transient transitions.");
				System.out.println("-jq: Quotienting w.r.t. iterated delayed/backward jumping simulation.");
				System.out.println("-jf: Trying to prove inclusion by jumping fair simulation in separate thread.");
				System.out.println("-jf2: Trying to prove inclusion by extra jumping fair simulation in separate thread (stronger but slower than -jf).");
				System.out.println("-fast: This abbreviates -b -rd -fplus -SFS -qr -c -eb -cpt -sp -de -blamin -blasub -tp -jq (Best performance.)");
				System.out.println("-fastc: Like -fast, except with -v and without -eb. Use this if you want counterexamples reported.");
				System.out.println("-finite:  Different semantics. Check inclusion of finite automata (not Buchi automata). Recommended.");
				System.out.println("-finite2: Check inclusion of finite automata by translating it to a Buchi inclusion problem. For comparison only. For best performance use -finite.");
				System.out.println("-par: Use parallel processing to speed things up.");
				System.out.println("-samp: Use Monte Carlo sampling to speed things up."); // LY added 
				System.exit(0);
			}
		}

		if(args.length<2){
		                System.out.println("RABIT v2.4.4 (Lookahead-simulation and Ramsey-based automata inclusion testing for Buchi automata (default) and NFA (with option -finite)).");
				System.out.println("Usage: java -jar RABIT.jar aut1.BA aut2.BA [-h -v -q -qr -c -rd -DFS -SFS -fplus -b -d -eb -cpt -sp -de -blamin -blasub -blaoffset n -blafixed n -tp -jq -jf -jf2 -fast -fastc] [-finite|-finite2] [-par]");

				System.out.println("Recommended use: java -jar RABIT.jar aut1.BA aut2.BA -fast");
				System.out.println("             or: java -jar RABIT.jar aut1.BA aut2.BA -fast -jf");
				System.out.println("For NFA        : java -jar RABIT.jar aut1.BA aut2.BA -fast -finite");
				System.out.println("\nOptions:");
				System.out.println("-h: Show this page");
				System.out.println("-v: Verbose mode");
				System.out.println("-v2: Very verbose mode");
				System.out.println("-q: Do quotienting w.r.t. forward simulation");
				System.out.println("-qr: Do fw/bw quotienting and removal of useless transitions repeatedly until a fixed point is reached. Overrides -q");
				System.out.println("-c: Use forward simulation between aut1 and aut2");
				System.out.println("-rd: Remove dead states");
				System.out.println("-DFS: Use DFS searching strategy (default: BFS strategy)");
				System.out.println("-SFS: Use smallest-first searching strategy (default: BFS strategy)");
				System.out.println("-fplus: Use one-step-further forward simulation");
				System.out.println("-b: Use backward simulation");
				System.out.println("-d: Debug mode");
				System.out.println("-eb: Earlier detection of counterexamples (with minimal overhead)");
				System.out.println("-cpt: Do a cheap pretest before subsumption checking.");
				System.out.println("-sp: Apply more extensive automata minimization and preprocessing. Only effective when used together with options -b -qr -rd.");
				System.out.println("-de: Use delayed simulation. Overrides -q.");
				System.out.println("-blamin: Use lookahead simulation in minimization.");
				System.out.println("-blasub: Use lookahead simulation for subsumption.");
				System.out.println("-blafixed n: Specify fixed lookahead n>=1. Overrides the automatic.");
				System.out.println("-blaoffset n: Increase automatic lookahead by integer n (can be negative)");
				System.out.println("-tp: Pruning of little brothers of transient transitions.");
				System.out.println("-jq: Quotienting w.r.t. iterated delayed/backward jumping simulation.");
				System.out.println("-jf: Trying to prove inclusion by jumping fair simulation in separate thread.");
				System.out.println("-jf2: Trying to prove inclusion by extra jumping fair simulation in separate thread (stronger but slower than -jf).");
				System.out.println("-fast: This abbreviates -b -rd -fplus -SFS -qr -c -eb -cpt -sp -de -blamin -blasub -tp -jq (Best performance.)");
				System.out.println("-fastc: Like -fast, except with -v and without -eb. Use this if you want counterexamples reported.");
				System.out.println("-finite:  Different semantics. Check inclusion of finite automata (not Buchi automata). Recommended.");
				System.out.println("-finite2: Check inclusion of finite automata by translating it to a Buchi inclusion problem. For comparison only. For best performance use -finite.");
				System.out.println("-par: Use parallel processing to speed things up.");
				System.out.println("-samp: Use Monte Carlo sampling to speed things up."); // LY added 
				return;
		}
		FiniteAutomaton aut1 = new FiniteAutomaton(args[0]);
		aut1.name=args[0];
		FiniteAutomaton aut2 = new FiniteAutomaton(args[1]);
		aut2.name=args[1];

		Options.quotient=false;
		Options.C1=false;
		Options.CPT=false;
		Options.EB=false;
		Options.backward=false;
		Options.opt2=true;
		Options.debug=false;
		Options.fplus=false;
		Options.rd=false;
		Options.DFS=false;
		Options.qr=false;
		Options.verbose=false;
		Options.very_verbose=false;
		Options.superpruning=false;
		Options.delayed=false;
		Options.finite=false;
		Options.finite2=false;				
		Options.blamin=false;
		Options.blasub=false;
		Options.blaoffset=0;
		Options.blafixed=1;
		Options.fast=false;
		Options.transient_pruning=false;
		Options.jumpsim_quotienting=false;
		Options.jumping_fairsim=false;
		Options.jumping_fairsim_extra=false;
		Options.par=false;
		Options.sampling = false;
		
		for(int i=2;i<args.length;i++){
			if(args[i].compareTo("-qr")==0){
				Options.qr=true;
			}
			if(args[i].compareTo("-q")==0){
				Options.quotient=true;
			}
			if(args[i].compareTo("-rd")==0){
				Options.rd=true;
			}
			if(args[i].compareTo("-c")==0){
				Options.C1=true;
			}
			if(args[i].compareTo("-eb")==0){
				Options.EB=true;
			}

			if(args[i].compareTo("-DFS")==0){
				Options.DFS=true;
			}
			if(args[i].compareTo("-SFS")==0){
				Options.SFS=true;
			}
			if(args[i].compareTo("-cpt")==0){
				Options.CPT=true;
			}
			if(args[i].compareTo("-b")==0){
				Options.backward=true;
			}
			if(args[i].compareTo("-fplus")==0){
				Options.fplus=true;
			}
			if(args[i].compareTo("-d")==0){
				Options.debug=true;
			}
			if(args[i].compareTo("-v")==0){
				Options.verbose=true;
			}
			if(args[i].compareTo("-v2")==0){
				Options.verbose=true;
				Options.very_verbose=true;
			}
			if(args[i].compareTo("-sp")==0){
				Options.superpruning=true;
			}
			if(args[i].compareTo("-de")==0){
				Options.delayed=true;
			}
			if(args[i].compareTo("-finite")==0){
				Options.finite=true;
			}
			if(args[i].compareTo("-finite2")==0){
				Options.finite2=true;
			}	
			if(args[i].compareTo("-antichain")==0){
				antichain=true;
			}
			if(args[i].compareTo("-blamin")==0){
			    Options.blamin=true;
			}
			if(args[i].compareTo("-blasub")==0){
			    Options.blasub=true;
			}
			if(args[i].compareTo("-blaoffset")==0){
			    Options.blaoffset=Integer.parseInt(args[i+1]);
			}
			if(args[i].compareTo("-blafixed")==0){
			    Options.blafixed=Integer.parseInt(args[i+1]);
			}
			if(args[i].compareTo("-tp")==0){
			    Options.transient_pruning=true;
			}
			if(args[i].compareTo("-jq")==0){
			    Options.jumpsim_quotienting=true;
			}
			if(args[i].compareTo("-jf")==0){
			    Options.jumping_fairsim=true;
			}
			if(args[i].compareTo("-jf2")==0){
			    Options.jumping_fairsim=true;
			    Options.jumping_fairsim_extra=true;
			}
			if(args[i].compareTo("-par")==0){
			    Options.par=true;
			}
			if(args[i].compareTo("-fast")==0){
			    Options.fast=true;
			    Options.backward=true;
			    Options.rd=true;
			    Options.fplus=true;
			    Options.SFS=true;
			    Options.qr=true;
			    Options.C1=true;
			    Options.EB=true;
			    Options.CPT=true;
			    Options.superpruning=true;
			    Options.delayed=true;
			    Options.blamin=true;
			    Options.blasub=true;
			    Options.transient_pruning=true;
			    Options.jumpsim_quotienting=true;
			}
			if(args[i].compareTo("-fastc")==0){
			    Options.fast=true;
			    Options.backward=true;
			    Options.rd=true;
			    Options.fplus=true;
			    Options.SFS=true;
			    Options.qr=true;
			    Options.C1=true;
			    Options.EB=false; // difference to fast. EB must be false to report counterexamples
			    Options.CPT=true;
			    Options.superpruning=true;
			    Options.delayed=true;
			    Options.blamin=true;
			    Options.blasub=true;
			    Options.transient_pruning=true;
			    Options.jumpsim_quotienting=true;
			    Options.verbose=true; // set verbose to true to report counterexample
			}
			if(args[i].compareTo("-samp") == 0) { // LY added 
			    Options.sampling = true;
			}
			
		}

		// Measure the time
		long ttime1=System.currentTimeMillis();

		if(Options.verbose){
		    // Display sizes of input automata
		    System.out.println("Aut A: # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
		    System.out.println("Aut B: # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
		}

		// Distinguish different cases of inclusion checking

		if(Options.finite){
		    if(Options.verbose) System.out.println("Checking inclusion of finite automata.");
		    if(Options.par){
			if(par_inclusion_finite(aut1, aut2)) 
			    System.out.println("Included.");
			else System.out.println("Not included.");
		    }
		    else{
			if(inclusion_finite(aut1, aut2)) 
			    System.out.println("Included.");
			else System.out.println("Not included.");
		    }
		}
		else if(Options.finite2){
		    if(Options.verbose) System.out.println("Translating finite automata inclusion to Buchi automata inclusion.");
		    aut1=toBA(aut1);
		    aut2=toBA(aut2);
		    if(Options.par){
			if(par_inclusion_Buchi(aut1, aut2)) 
			    System.out.println("Included.");
			else System.out.println("Not included.");
		    }
		    else{
			if(inclusion_Buchi(aut1, aut2)) 
			    System.out.println("Included.");
			else System.out.println("Not included.");			
		    }
		}
		else if(!antichain){
		    if(Options.par){
			if(par_inclusion_Buchi(aut1, aut2)) 
			    System.out.println("Included.");
			else System.out.println("Not included.");
		    }
		    else{
			if(inclusion_Buchi(aut1, aut2)) 
			    System.out.println("Included.");
			else System.out.println("Not included.");
		    }
		}else{
		    InclusionAnti inclusion=new InclusionAnti(aut1,aut2);
		    inclusion.run();
		    if(inclusion.isIncluded())
			System.out.println("Included");
		    else System.out.println("Not Included");
		    }

		long ttime2=System.currentTimeMillis();
		if(Options.verbose) System.out.println("Time used(ms): "+(ttime2-ttime1)+".");
    }
    
    // -----------------------------------------------------------------------------------------------------------
    // following methods are added by Yong Li
    private static FiniteAutomaton copyAutomaton(FiniteAutomaton aut) {
        FiniteAutomaton autCopy = new FiniteAutomaton();
        
        FAState initAut = aut.getInitialState();
        Map<Integer, FAState> stMap = new TreeMap<>();
        FAState initCopy = autCopy.createState();
        autCopy.setInitialState(initCopy);
        stMap.put(initAut.id, initCopy);
        if(aut.F.contains(initAut)) {
            autCopy.F.add(initCopy);
        }
        
        Queue<FAState> queue = new LinkedList<>();
        queue.add(initAut);
        while(! queue.isEmpty()) {
            FAState autState = queue.poll();
            FAState copyState = stMap.get(autState.id);
            Iterator<String> strIt = autState.nextIt();
            while(strIt.hasNext()) {
                String label = strIt.next();
                Set<FAState> stateSuccs = autState.getNext(label);
                for(FAState stateSucc : stateSuccs) {
                    FAState copySucc = stMap.get(stateSucc.id);
                    if(copySucc == null) {
                        copySucc = autCopy.createState();
                        stMap.put(stateSucc.id, copySucc);
                        queue.add(stateSucc);
                    }
                    autCopy.addTransition(copyState, copySucc, label);
                    if(aut.F.contains(stateSucc)) {
                        autCopy.F.add(copySucc);
                    }
                }
            }
        }
        
        return autCopy;
    }
    
    private static String prefixStr = null;
    private static String suffixStr = null;
    
    // following is for ROLL
    public static boolean isIncluded(FiniteAutomaton A, FiniteAutomaton B) {
        // first set all flags 
        Options.debug = false;
        Options.fast=true;
        Options.backward=true;
        Options.rd=true;
        Options.fplus=true;
        Options.SFS=true;
        Options.qr=true;
        Options.C1=true;
        Options.EB=false; // difference to fast. EB must be false to report counterexamples
        Options.CPT=true;
        Options.superpruning=true;
        Options.delayed=true;
        Options.blamin=true;
        Options.blasub=true;
        Options.transient_pruning=true;
        Options.jumpsim_quotienting=true;
        Options.verbose=false; // set verbose to true to report counterexample
        
        // copy the automata
        FiniteAutomaton aut1 = copyAutomaton(A);
        FiniteAutomaton aut2 = copyAutomaton(B);
        
        // now we do the inclusion check
        Minimization Minimizer = new Minimization();
        // First do a lightweight preprocessing
        AutomatonPreprocessingResult x = Minimizer.Lightweight_Preprocess_Buchi(aut1, aut2);
        aut1 = x.system;
        aut2 = x.spec;
        if (Options.verbose) {
            System.out.println("Aut A (after light preprocessing): # of Trans. " + aut1.trans + ", # of States "
                    + aut1.states.size() + ".");
            System.out.println("Aut B (after light preprocessing): # of Trans. " + aut2.trans + ", # of States "
                    + aut2.states.size() + ".");
        }
        if (x.result) {
            if (Options.verbose)
                System.out.println("Included (already proven during lightweight preprocessing).");
            return true;
        }

        // Now, if the automata are not too large,
        // try a short run of the Ramsey algorithm (<= 50 metagraphs), in the
        // hope of solving the problem without heavy preprocessing
        if (aut1.states.size() + aut2.states.size() <= 400) {
            if (Options.verbose)
                System.out.println("Trying Ramsey method with small bound (50 metagraphs).");

            InclusionOptBVLayered inclusion = new InclusionOptBVLayered(aut1, aut2, 50);
            inclusion.run();
            if (!inclusion.timeout) {
                if (Options.verbose)
                    System.out.println("Solved. Metagraphs added to the Next set: " + inclusion.mggen);
                if (inclusion.isIncluded())
                    return true;
                else {
                    prefixStr = inclusion.counterexample_prefix;
                    suffixStr = inclusion.counterexample_loop;
                    if (Options.verbose)
                        System.out.println("Counterexample: " + inclusion.counterexample_prefix + " ("
                                + inclusion.counterexample_loop + ")");
                    return false;
                }
            } else if (Options.verbose)
                System.out.println("Light methods alone could not solve it. Trying heavy preprocessing.");
        } else if (Options.verbose)
            System.out.println("Automata still too large. Trying heavy preprocessing.");

        // Now do the heavy preprocessing (and later possibly full Ramsey).
        x = Minimizer.Preprocess_Buchi(aut1, aut2);
        aut1 = x.system;
        aut2 = x.spec;
        if (Options.verbose) {
            System.out.println("Aut A after minimization: # of Trans. " + aut1.trans + ", # of States "
                    + aut1.states.size() + ".");
            System.out.println("Aut B after minimization: # of Trans. " + aut2.trans + ", # of States "
                    + aut2.states.size() + ".");
        }
        if (x.result) {
            if (Options.verbose)
                System.out.println("Included (already proven during preprocessing)");
            return true;
        } else {
            Options.globalstop = false;
            FairsimThread fst = null;
            if (Options.jumping_fairsim) {
                fst = new FairsimThread(aut1, aut2);
                fst.start();
            }
            // Start Ramsey procedure with limit==0, which means no limit.
            InclusionOptBVLayered inclusion = new InclusionOptBVLayered(aut1, aut2, 0);
            inclusion.run();
            if (Options.jumping_fairsim)
                fst.stop();
            if (Options.verbose)
                System.out.println("Metagraphs added to the Next set: " + inclusion.mggen);
            if (inclusion.isIncluded())
                return true;
            else {
                prefixStr = inclusion.counterexample_prefix;
                suffixStr = inclusion.counterexample_loop;
                if (Options.verbose)
                    System.out.println("Counterexample: " + inclusion.counterexample_prefix + " ("
                            + inclusion.counterexample_loop + ")");
                return false;
            }
        }
    }
    
    public static boolean isIncludedPar(FiniteAutomaton A, FiniteAutomaton B){
        // first set all flags 
        Options.debug = false;
        Options.fast=true;
        Options.backward=true;
        Options.rd=true;
        Options.fplus=true;
        Options.SFS=true;
        Options.qr=true;
        Options.C1=true;
        Options.EB=false; // difference to fast. EB must be false to report counterexamples
        Options.CPT=true;
        Options.superpruning=true;
        Options.delayed=true;
        Options.blamin=true;
        Options.blasub=true;
        Options.transient_pruning=true;
        Options.jumpsim_quotienting=true;
        Options.verbose=false; // set verbose to true to report counterexample
        Options.par = true;
        
        // copy the automata
        FiniteAutomaton aut1 = copyAutomaton(A);
        FiniteAutomaton aut2 = copyAutomaton(B);
        
        ParallelMinimization Minimizer = new ParallelMinimization();
        // First do a lightweight preprocessing
        AutomatonPreprocessingResult x = Minimizer.Lightweight_Preprocess_Buchi(aut1, aut2);
        aut1=x.system;
        aut2=x.spec;
        if(Options.verbose){
            System.out.println("Aut A (after light preprocessing): # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
            System.out.println("Aut B (after light preprocessing): # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
        }
        if(x.result){
            if(Options.verbose) System.out.println("Included (already proven during lightweight preprocessing).");
            return true;
        }
        
        // Now, if the automata are not too large, 
        // try a short run of the Ramsey algorithm (<= 50 metagraphs), in the hope of solving the problem without heavy preprocessing
        if(aut1.states.size()+aut2.states.size() <= 400){
            if(Options.verbose) System.out.println("Trying Ramsey method with small bound (50 metagraphs).");
            
            InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1,aut2,50);
            inclusion.run();
            if(!inclusion.timeout){
            if(Options.verbose) System.out.println("Solved. Metagraphs added to the Next set: "+inclusion.mggen);
            if(inclusion.isIncluded()) return true; else {
                prefixStr = inclusion.counterexample_prefix;
                suffixStr = inclusion.counterexample_loop;
                if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix+" ("+inclusion.counterexample_loop+")");
                return false;
            }
            }
            else if(Options.verbose) System.out.println("Light methods alone could not solve it. Trying heavy preprocessing.");
        }
        else if(Options.verbose) System.out.println("Automata still too large. Trying heavy preprocessing.");
        
        // Now do the heavy preprocessing (and later possibly full Ramsey).
        x = Minimizer.Preprocess_Buchi(aut1, aut2);
        aut1=x.system;
        aut2=x.spec;
        if(Options.verbose){
            System.out.println("Aut A after minimization: # of Trans. "+ aut1.trans + ", # of States " + aut1.states.size()+".");
            System.out.println("Aut B after minimization: # of Trans. "+ aut2.trans + ", # of States " + aut2.states.size()+".");
        }
        if(x.result){
            if(Options.verbose) System.out.println("Included (already proven during preprocessing)");
            return true;
        }
        else{
            Options.globalstop=false;
            FairsimThread fst=null;
            if(Options.jumping_fairsim){
            fst = new FairsimThread(aut1, aut2);
            fst.start();
            }
            // Start Ramsey procedure with limit==0, which means no limit.
            InclusionOptBVLayered inclusion=new InclusionOptBVLayered(aut1,aut2,0);
            inclusion.run();
            if(Options.jumping_fairsim) fst.stop();
            if(Options.verbose) System.out.println("Metagraphs added to the Next set: "+inclusion.mggen);
            if(inclusion.isIncluded()) return true; else {
                prefixStr = inclusion.counterexample_prefix;
                suffixStr = inclusion.counterexample_loop;
            if(Options.verbose) System.out.println("Counterexample: "+inclusion.counterexample_prefix+" ("+inclusion.counterexample_loop+")");
            return false;
            }
        }
}
    
    public static String getPrefix() {
        return prefixStr;
    }
    
    public static String getSuffix() {
        return suffixStr;
    }
    // -----------------------------------------------------------------------------------------------------------
}


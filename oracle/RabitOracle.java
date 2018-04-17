/* Written by Yong Li                                                     */
/* Copyright (c) 2016                  	                                  */
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

package oracle;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeMap;

import algorithms.InclusionOptBVLayered;
import algorithms.Minimization;
import algorithms.Options;
import algorithms.Simulation;
import automata.AutomatonPreprocessingResult;
import automata.FAState;
import automata.FiniteAutomaton;

/**
 * @author liyong 
 * liyong@ios.ac.cn
 * adapted from RABIT.java
 * */
public class RabitOracle {

	private final FiniteAutomaton automaton;
	private final Membership membership;
	
	private String prefixCE;  // for finite prefix
	private String suffixCE;  //
	
	// default
	private boolean largerFirst = true;
	
	public RabitOracle(FiniteAutomaton aut) {
        assert aut != null;
		this.automaton = aut;
		Options.fast = true;
		Options.backward = true;
		Options.rd = true;
		Options.fplus = true;
		Options.SFS = true;
		Options.qr = true;
		Options.C1 = true;
		Options.EB = false; // difference to fast. EB must be false to report
							// counterexamples
		Options.CPT = true;
		Options.superpruning = true;
		Options.delayed = true;
		Options.blamin = true;
		Options.blasub = true;
		Options.transient_pruning = true;
		Options.jumpsim_quotienting = true;
		Options.verbose = true; // set verbose to true to report counterexample
		membership = new Membership(aut);
	}
	
	public FiniteAutomaton getTarget() {
		return automaton;
	}
	
	public void setVerbose() {
		Options.verbose = true;
	}

	//TODO
	public boolean isAccepted(List<String> word) {
		return membership.checkMembership(word);
	}
	
	public void resetLargerFirst() {
		largerFirst = false;
	}
	
	// determine whether an infinite word is accepting
	public boolean isAccepted(List<String> prefix, List<String> suffix) {
		return membership.checkMembership(prefix, suffix);
	}

	public EqResult isEqualBuechi(FiniteAutomaton aut) {
		FiniteAutomaton aut1 = copyAutomaton(automaton);
		FiniteAutomaton aut2 = copyAutomaton(aut);
		
		// is aut1 smaller than aut2
		boolean changeOrder = compare(aut1, aut2);
        // is target a subset of given automaton
		EqResult result = new EqResult();
		result.isEqual = true;
		
		if(! largerFirst) changeOrder = false;
		
		if(changeOrder) {
            // aut2 is larger than aut1
			if(! buechiInclude(aut2, aut1)) {
				result.isCeInTarget = false;
				result.isEqual = false;
				return result;
			}
			aut1 = copyAutomaton(automaton);
			aut2 = copyAutomaton(aut);
			// is given automaton a subsetof target
			if(! buechiInclude(aut1, aut2)) {
				result.isCeInTarget = true;
				result.isEqual = false;
				return result;
			}
			
		}else {
            // aut1 is larger than aut2
			if(! buechiInclude(aut1, aut2)) {
				result.isCeInTarget = true;
				result.isEqual = false;
				return result;
			}
			aut1 = copyAutomaton(automaton);
			aut2 = copyAutomaton(aut);
			// is given automaton a subsetof target
			if(! buechiInclude(aut2, aut1)) {
				result.isCeInTarget = false;
				result.isEqual = false;
				return result;
			}
		}
		
		return result;
	}
	
	private boolean compare(FiniteAutomaton aut1, FiniteAutomaton aut2) {
		// aut1 < aut2
		if(aut1.states.size() < aut2.states.size()) return true;
		if(aut2.states.size() < aut1.states.size()) return false;
		// number of states are equal
		if(aut1.trans < aut2.trans) return true;
		if(aut2.trans < aut1.trans) return false;
		return true;
	}
	
	private void normalizeCounterExample(FiniteAutomaton aut) {
		
		
		String[] preArr = prefixCE.split("");
		List<String> pre = new ArrayList<>(preArr.length);
		for(int i = 0; i < preArr.length; i ++) {
			pre.add(preArr[i]);
		}
		String[] sufArr = suffixCE.split("");
		List<String> suf = new ArrayList<>(sufArr.length);
		for(int i = 0; i < sufArr.length; i ++) {
			suf.add(sufArr[i]);
		}
		
		FiniteAutomaton product = ProductBuilder.build(aut, pre, suf);
		EmptinessCheck checker = new EmptinessCheck(product);
		boolean result = checker.isEmpty();
		if(result) {
			System.err.println("Error, word should be in the automaton");
			System.exit(-1);
		}
		checker.findpath();
		List<String> prefix = checker.getInifinteWord().getLeft();
		List<String> suffix = checker.getInifinteWord().getRight();
		prefixCE = "";
		for(int i = 0; i < prefix.size(); i ++) {
			prefixCE += prefix.get(i);
		}
		
		suffixCE = "";
		for(int i = 0; i < suffix.size(); i ++) {
			suffixCE += suffix.get(i);
		}
		
		if(Options.verbose) {
			System.out.println("normalized ce: " + prefixCE + " (" + suffixCE + ")");
		}
		
	}
	
	public String getPrefix() {
		return prefixCE;
	}
	
	public String getSuffix() {
		return suffixCE;
	}
	
	
	private FiniteAutomaton copyAutomaton(FiniteAutomaton aut) {
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
	// TODO
	public boolean isEqualFA(FiniteAutomaton aut) {
		return false;
	}

	// NOTE both arguments will be modified
	private boolean buechiInclude(FiniteAutomaton aut1, FiniteAutomaton aut2) {
		// initialization
		prefixCE = null;
		suffixCE = null;
		
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
					prefixCE = inclusion.counterexample_prefix;
					suffixCE = inclusion.counterexample_loop;
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
				prefixCE = inclusion.counterexample_prefix;
				suffixCE = inclusion.counterexample_loop;
				if (Options.verbose)
					System.out.println("Counterexample: " + inclusion.counterexample_prefix + " ("
							+ inclusion.counterexample_loop + ")");
				return false;
			}
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

			int la = 1;

			if (Options.jumping_fairsim_extra) {
				while (true) {
					if ((la % 2) == 1) {
						if (Options.verbose)
							System.out.println("Computing X_C_jumping fair sim with la: " + la);
						if (sim.x_JumpingBLAFairSimRelNBW(system, spec, la, 2)) {
							if (Options.verbose)
								System.out
										.println("X_C_Jumping fairsim proved inclusion first at lookahead " + la + ".");
							Options.globalstop = true;
							return;
						}
					} else {
						if (Options.verbose)
							System.out.println("Computing X Segment_jumping fair sim with la: " + la);
						if (sim.x_JumpingBLAFairSimRelNBW(system, spec, la, 3)) {
							if (Options.verbose)
								System.out.println(
										"X Segment_Jumping fairsim proved inclusion first at lookahead " + la + ".");
							Options.globalstop = true;
							return;
						}
					}
					la++;
				}
			} else {
				while (true) {
					if ((la % 2) == 1) {
						if (Options.verbose)
							System.out.println("Computing C_jumping fair sim with la: " + la);
						if (sim.JumpingBLAFairSimRelNBW(system, spec, la, 2)) {
							if (Options.verbose)
								System.out.println("C_Jumping fairsim proved inclusion first at lookahead " + la + ".");
							Options.globalstop = true;
							return;
						}
					} else {
						if (Options.verbose)
							System.out.println("Computing Segment_jumping fair sim with la: " + la);
						if (sim.JumpingBLAFairSimRelNBW(system, spec, la, 3)) {
							if (Options.verbose)
								System.out.println(
										"Segment_Jumping fairsim proved inclusion first at lookahead " + la + ".");
							Options.globalstop = true;
							return;
						}
					}
					la++;
				}
			}
		}
	}
	
	

}

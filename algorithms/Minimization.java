/* Written by Yu-Fang Chen, Richard Mayr, and Chih-Duo Hong               */
/* Copyright (c) 2011                  	                                  */
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

package algorithms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;
import automata.AutomatonPreprocessingResult;
import comparator.StateComparator;
import comparator.StatePairComparator;
import datastructure.HashSet;
import datastructure.Pair;
import datastructure.State_Label;
import algorithms.Simulation;

/** This is for minimizing and otherwise preprocessing Buchi-automata by using simulation-based techniques.
 *  It uses the code for computing the simulations from Simulation.java.
 * 
 * @author Richard Mayr
 * 
 */
public class Minimization{


    // The creates a new automaton without the dead states in automaton aut 
    // i.e., no states that are not reachable from the initial state 
    // and do states that cannot reach any accepting loop.
    // The preserves the omega-labguage, but not the finite language.
    // A new automaton is returned. The argument aut is not modified.

	public FiniteAutomaton removeDead(FiniteAutomaton aut) {
		FiniteAutomaton result = new FiniteAutomaton();
		result.name = aut.name;
		HashSet<FAState> finalReachable = new HashSet<FAState>();

		SCC s = new SCC(aut, true);
		finalReachable.addAll(s.getResult());

		while (true) {
			HashSet<FAState> toAdd = new HashSet<FAState>();
			Iterator<FAState> finalReachable_it = finalReachable.iterator();
			while (finalReachable_it.hasNext()) {
				FAState end = finalReachable_it.next();
				toAdd.addAll(end.getPre());
			}
			toAdd.removeAll(finalReachable);
			if (toAdd.size() == 0)
				break;
			finalReachable.addAll(toAdd);
		}

		HashMap<FAState, FAState> stMap = new HashMap<FAState, FAState>();
		HashSet<FAState> toProcess = new HashSet<FAState>();
		toProcess.add(aut.getInitialState());
		result.setInitialState(result.createState());
		stMap.put(aut.getInitialState(), result.getInitialState());
		if (aut.F.contains(aut.getInitialState()))
			result.F.add(result.getInitialState());

		while (true) {
			HashSet<FAState> toAdd = new HashSet<FAState>();
			Iterator<FAState> toProcess_it = toProcess.iterator();
			while (toProcess_it.hasNext()) {
				FAState begin = toProcess_it.next();
				Iterator<String> sym_it = begin.nextIt();
				while (sym_it.hasNext()) {
					String sym = sym_it.next();
					Iterator<FAState> end_it = begin.getNext(sym).iterator();
					while (end_it.hasNext()) {
						FAState end = end_it.next();
						if (finalReachable.contains(end)) {
							if (!stMap.containsKey(end)) {
								toAdd.add(end);
								stMap.put(end, result.createState());
								if (aut.F.contains(end))
									result.F.add(stMap.get(end));
							}
							result.addTransition(stMap.get(begin),
									stMap.get(end), sym);
						}
					}
				}
			}
			if (toAdd.size() == 0)
				break;
			toProcess.clear();
			toProcess.addAll(toAdd);
		}
		return result;
	}


    // The creates a new automaton without the dead states in automaton aut 
    // i.e., no states that are not reachable from the initial state 
    // and do states that cannot reach any accepting state. (NOT accepting loop.)
    // The preserves the finite-word language.
    // A new automaton is returned. The argument aut is not modified.

	public FiniteAutomaton finite_removeDead(FiniteAutomaton aut) {
		FiniteAutomaton result = new FiniteAutomaton();
		result.name = aut.name;
		HashSet<FAState> finalReachable = new HashSet<FAState>();

		finalReachable.addAll(aut.F);

		while (true) {
			HashSet<FAState> toAdd = new HashSet<FAState>();
			Iterator<FAState> finalReachable_it = finalReachable.iterator();
			while (finalReachable_it.hasNext()) {
				FAState end = finalReachable_it.next();
				toAdd.addAll(end.getPre());
			}
			toAdd.removeAll(finalReachable);
			if (toAdd.size() == 0)
				break;
			finalReachable.addAll(toAdd);
		}

		HashMap<FAState, FAState> stMap = new HashMap<FAState, FAState>();
		HashSet<FAState> toProcess = new HashSet<FAState>();
		toProcess.add(aut.getInitialState());
		result.setInitialState(result.createState());
		stMap.put(aut.getInitialState(), result.getInitialState());
		if (aut.F.contains(aut.getInitialState()))
			result.F.add(result.getInitialState());

		while (true) {
			HashSet<FAState> toAdd = new HashSet<FAState>();
			Iterator<FAState> toProcess_it = toProcess.iterator();
			while (toProcess_it.hasNext()) {
				FAState begin = toProcess_it.next();
				Iterator<String> sym_it = begin.nextIt();
				while (sym_it.hasNext()) {
					String sym = sym_it.next();
					Iterator<FAState> end_it = begin.getNext(sym).iterator();
					while (end_it.hasNext()) {
						FAState end = end_it.next();
						if (finalReachable.contains(end)) {
							if (!stMap.containsKey(end)) {
								toAdd.add(end);
								stMap.put(end, result.createState());
								if (aut.F.contains(end))
									result.F.add(stMap.get(end));
							}
							result.addTransition(stMap.get(begin),
									stMap.get(end), sym);
						}
					}
				}
			}
			if (toAdd.size() == 0)
				break;
			toProcess.clear();
			toProcess.addAll(toAdd);
		}
		return result;
	}



	/**
	 * Simplify a finite automaton by merging simulation equivalent states
	 * 
	 * @param fa
	 *            : a finite automaton
	 * @param Sim
	 *            : some simulation rel_specation over states in the spec
	 *            automaton
	 * 
	 * @return an equivalent finite automaton
	 */
	public FiniteAutomaton quotient(FiniteAutomaton fa, Set<Pair<FAState, FAState>> rel) {
		FiniteAutomaton result = new FiniteAutomaton();
		result.name = fa.name;
		TreeMap<FAState, FAState> map = new TreeMap<FAState, FAState>();
		TreeMap<FAState, FAState> reducedMap = new TreeMap<FAState, FAState>();

		Iterator<FAState> state_it = fa.states.iterator();
		while (state_it.hasNext()) {
			FAState state = state_it.next();
			map.put(state, state);
			Iterator<FAState> state_it2 = fa.states.iterator();
			while (state_it2.hasNext()) {
				FAState state2 = state_it2.next();
				if (rel.contains(new Pair<FAState, FAState>(state, state2))
						&& rel.contains(new Pair<FAState, FAState>(state2,
								state))) {
					map.put(state, state2);
				}
			}
		}

		FAState init = result.createState();
		reducedMap.put(map.get(fa.getInitialState()), init);
		result.setInitialState(init);

		state_it = fa.states.iterator();
		while (state_it.hasNext()) {
			FAState state = state_it.next();
			if (!reducedMap.containsKey(map.get(state))) {
				reducedMap.put(map.get(state), result.createState());
			}
			if (fa.F.contains(state)) {
				result.F.add(reducedMap.get(map.get(state)));
			}
			Iterator<String> sym_it = state.nextIt();
			while (sym_it.hasNext()) {
				String sym = sym_it.next();
				Iterator<FAState> to_it = state.getNext(sym).iterator();
				while (to_it.hasNext()) {
					FAState to = to_it.next();
					if (!reducedMap.containsKey(map.get(to))) {
						reducedMap.put(map.get(to), result.createState());
					}
					result.addTransition(reducedMap.get(map.get(state)),
							reducedMap.get(map.get(to)), sym);
				}
			}
		}
		Set<Pair<FAState, FAState>> newrel = new TreeSet<Pair<FAState, FAState>>(
				new StatePairComparator());
		Iterator<Pair<FAState, FAState>> sim_it = rel.iterator();
		while (sim_it.hasNext()) {
			Pair<FAState, FAState> sim = sim_it.next();
			FAState left, right;
			if (sim.getLeft().getowner() == fa) {
				left = reducedMap.get(map.get(sim.getLeft()));
			} else {
				left = sim.getLeft();
			}

			if (sim.getRight().getowner() == fa) {
				right = reducedMap.get(map.get(sim.getRight()));
			} else {
				right = sim.getRight();
			}
			newrel.add(new Pair<FAState, FAState>(left, right));
		}
		rel.clear();
		rel.addAll(newrel);

		return result;
	}



	// This is to compute the set of reachable states of the symchronized product of automata fa and fa2.
    
	    private TreeMap<FAState, Set<FAState>> compute_reach_product(FiniteAutomaton fa, FiniteAutomaton fa2){
		
		TreeMap<FAState, Set<FAState>> result = new TreeMap<FAState, Set<FAState>>();
		TreeSet<Pair<FAState, FAState>> next = new TreeSet<Pair<FAState, FAState>>(new StatePairComparator());

		next.add(new Pair<FAState, FAState>(fa.getInitialState(), fa2.getInitialState()));
		while(!next.isEmpty()){
		    Pair<FAState, FAState> pair = next.first();
		    next.remove(pair);
		    if(!result.containsKey(pair.getLeft())){
			Set<FAState> sts = new TreeSet<FAState>();
			result.put(pair.getLeft(), sts);
		    }
		    result.get(pair.getLeft()).add(pair.getRight());
		    
		    Iterator<String> sym_it = pair.getLeft().nextIt();
		    while(sym_it.hasNext()){
				String sym=sym_it.next();
				Set<FAState> sym_succ_L = pair.getLeft().getNext(sym);
				Set<FAState> sym_succ_R = pair.getRight().getNext(sym);
				if(sym_succ_R==null) continue;
				Iterator<FAState> it1 = sym_succ_L.iterator();
				while(it1.hasNext()){
				    	FAState state1=it1.next();
					Iterator<FAState> it2 = sym_succ_R.iterator();
					while(it2.hasNext()){
					    FAState state2=it2.next();
					    if(next.contains(new Pair<FAState,FAState>(state1,state2))) continue;
					    if(result.containsKey(state1)) 
						{
						    if(result.get(state1).contains(state2)) continue;
						}
					    next.add(new Pair<FAState, FAState>(state1, state2));
					}
				}
		    }
   		}
		return result;
	    }


	    // If no state in set has an outgoing transition with a given symbol x,
	    // then state does not need transitions with label x either.
	    // Returns the number of removed transitions.
	   private int sym_obsolete_pruning(Set<FAState> set, FAState state)
	    {
		int result=0;
		Iterator<String> sym_it = state.nextIt();
		while(sym_it.hasNext()){
					String sym=sym_it.next();
					if(no_such_label(sym, set)) 
					    {
						Iterator<FAState> state_it2=state.getNext(sym).iterator();
						while(state_it2.hasNext()){
						    FAState state2=state_it2.next();
						    state2.getPre(sym).remove(state);
						}
						result += state.getNext(sym).size();
						state.getNext(sym).clear();
					    }
		}
		return result;
	    }


    private boolean no_such_label(String sym, Set<FAState> set)
    {
	Iterator<FAState> state_it=set.iterator();
	while(state_it.hasNext()){
	    FAState state2=state_it.next();
	    if(state2.getNext(sym) != null) return false; 
	}
	return true;
    }

    // Richard: Automaton fa2 (i.e., spec) is pruned by removing states that are unreachable in the 
    // product with fa (i.e., system), and some unnecessary transitions, too.
    // It returns the number of removed states, plus the number of extra removed transitions,
    // i.e., nonzero iff something changed.
        public int product_pruning(FiniteAutomaton fa, FiniteAutomaton fa2){
	    int result=0;
	    Set<FAState> to_remove=new TreeSet<FAState>();
	    // Compute the reachable states in the product. There reverse order fa2, fa is deliberate.
	    TreeMap<FAState, Set<FAState>> product = compute_reach_product(fa2, fa);
	    Iterator<FAState> state_it=fa2.states.iterator();
	    while(state_it.hasNext()){
		    FAState state=state_it.next();
		    if(!product.containsKey(state)) to_remove.add(state); 
		    else {
			int x = sym_obsolete_pruning(product.get(state), state);
			fa2.trans -= x;
			result += x;
		    }
	    }
	    state_it = to_remove.iterator();
	    while(state_it.hasNext()){
		    FAState state=state_it.next();
		    //System.out.println("Removing state "+state.getID());
		    fa2.removeState(state);
		    result++;
	    }
	    return result;
	}



	// Richard: Given a fully fw/bw quotiented automaton without fw/bw little brothers.
	// Given a fw and a bw simulation.
	// Remove transitions in fa that could be removed by the criterion that a fw and bw 'better' transition exists in fa2.
        // This is only correct in the following two cases:
        // 1. fw_rel is forward direct simulation and bw_rel is a preorder underapproximating bw direct trance inclusion.
        // 2. fw_rel is a preorder underapproximating fw direct trance inclusion and bw_rel is bw direct simulation.
        // Note: Using direct trance inclusion for both fw_rel and bw_rel is wrong! 
        // Return value: the number of removed transitions, i.e., 0 iff noting changes.
        // The argument fa is changed by this method.

    public int removed_trans_extra(FiniteAutomaton fa, FiniteAutomaton fa2, Set<Pair<FAState,FAState>> fw_rel, Set<Pair<FAState,FAState>> bw_rel) {
		int result=0;
		Set<FAState> to_remove=new TreeSet<FAState>();

		Iterator<FAState> state_it=fa.states.iterator();
		while(state_it.hasNext()){
		    FAState state=state_it.next();
		    Iterator<String> sym_it = state.nextIt();
		    while(sym_it.hasNext()){
				String sym=sym_it.next();
				Iterator<FAState> deststate_it = state.getNext(sym).iterator();
				while(deststate_it.hasNext()){
				    FAState deststate=deststate_it.next();
				    if (exists_better_trans(fa2, state, sym, deststate, fw_rel, bw_rel)) 
					{
					    to_remove.add(deststate);
					}
				}
				
				if(to_remove.size() >0) 
				    {
					Iterator<FAState> it3=to_remove.iterator();
					    while(it3.hasNext()){
						FAState state3=it3.next();
						    state3.getPre(sym).remove(state);
							}
					    state.getNext(sym).removeAll(to_remove);
					    fa.trans = fa.trans - to_remove.size();
					    result += to_remove.size();
					    to_remove.clear();
				    }
		    }
		}
		return result;
	}

	// Richard: Aux. test for removable_trans_extra

	    private boolean exists_better_trans(FiniteAutomaton fa2, FAState state, String sym, FAState deststate, Set<Pair<FAState,FAState>> fw_rel, Set<Pair<FAState,FAState>> bw_rel){

		Iterator<FAState> other_state_it=fa2.states.iterator();
		while(other_state_it.hasNext()){
		    FAState other_state=other_state_it.next();
		    if(state==other_state) continue;
   		    if(other_state.getNext(sym) != null) 
			{
			    Iterator<FAState> other_deststate_it = other_state.getNext(sym).iterator();
				while(other_deststate_it.hasNext()){
				    FAState other_deststate = other_deststate_it.next();
				    if(deststate==other_deststate) continue;
				    if(bw_rel.contains(new Pair<FAState,FAState>(state,other_state)) && fw_rel.contains(new Pair<FAState,FAState>(deststate,other_deststate))) return true;
				}
			}
		}
		return false;
		}




	/**
	 * Prune automaton by eliminating fw little brothers originated from oristate via sym wrt. fw simulation relation rel
	 * @author Richard Mayr
	 * @param oristate
	 *            : origianl state
	 * @param sym
	 *            : transition symbols
     * @param stateset
     *            : set of states that can be reached from oristate via sym
	 * @param rel 
	 *            : fw simulation relation
	 * 
	 * @return the number of removed transitions
	 */

	
	private int prune_fw_set(FAState oristate, String sym, Set<FAState> stateset, Set<Pair<FAState,FAState>> rel) {
	    Set<FAState> to_remove=new TreeSet<FAState>();
	    Iterator<FAState> it1=stateset.iterator();
	    while(it1.hasNext()){
			FAState state=it1.next();
			Iterator<FAState> it2=stateset.iterator();
	        while(it2.hasNext()){
			    FAState state2=it2.next();
			    if(rel.contains(new Pair<FAState,FAState>(state,state2)) && !rel.contains(new Pair<FAState,FAState>(state2,state))) { 
			    	to_remove.add(state); 
				    break; 
				}
	        }
	    }
	    if(to_remove.size() >0) 
		{
		    Iterator<FAState> it3=to_remove.iterator();
		    while(it3.hasNext()){
			    FAState state3=it3.next();
			    state3.getPre(sym).remove(oristate);
		    }
		    stateset.removeAll(to_remove);
		}
	    return to_remove.size();
	}

	/**
	 * Prune automaton by eliminating fw little brothers wrt. fw simulation relation rel
	 * @author Richard Mayr
     * @param fa
     *            : The source automaton
	 * @param rel 
	 *            : fw simulation relation
	 */

	public void prune_fw(FiniteAutomaton fa, Set<Pair<FAState,FAState>> rel) {
		Iterator<FAState> state_it=fa.states.iterator();
		while(state_it.hasNext()){
		    FAState state=state_it.next();
		    Iterator<String> sym_it = state.nextIt();
		    while(sym_it.hasNext()){
				String sym=sym_it.next();
				Set<FAState> sym_succ=state.getNext(sym);
				fa.trans = fa.trans - prune_fw_set(state, sym, sym_succ, rel);
		    }
		}
	}


	

	/**
	 * Prune automaton by eliminating bw little brothers that can reach deststate via sym wrt. bw simulation relation rel
	 * @author Richard Mayr
	 * @param deststate
	 *            : destination state
	 * @param sym
	 *            : transition symbols
     * @param stateset
     *            : set of states that can reach deststate via sym
	 * @param rel 
	 *            : bw simulation relation
	 * 
	 * @return the number of removed transitions
	 */
	
    private int prune_bw_set(FAState deststate, String sym, Set<FAState> stateset, Set<Pair<FAState,FAState>> rel) {
	    Set<FAState> to_remove=new TreeSet<FAState>();
	    Iterator<FAState> it1=stateset.iterator();
	    while(it1.hasNext()){
			FAState state=it1.next();
			Iterator<FAState> it2=stateset.iterator();
	        while(it2.hasNext()){
		    FAState state2=it2.next();
		    	if(rel.contains(new Pair<FAState,FAState>(state,state2)) && !rel.contains(new Pair<FAState,FAState>(state2,state))) { 
		    		to_remove.add(state); 
		    		break; 
			    }
	        }
	    }
	    if(to_remove.size() >0) {
		    Iterator<FAState> it3=to_remove.iterator();
		    while(it3.hasNext()){
			    FAState state3=it3.next();
			    state3.getNext(sym).remove(deststate);
		    }
		    stateset.removeAll(to_remove);
		}
	    return to_remove.size();
	}

	/**
	 * Prune automaton by eliminating bw little brothers wrt. bw simulation relation rel
	 * @author Richard Mayr
     * @param fa
     *            : The source automaton
	 * @param rel 
	 *            : fw simulation relation
	 */

    public void prune_bw(FiniteAutomaton fa, Set<Pair<FAState,FAState>> rel) {
		Iterator<FAState> state_it=fa.states.iterator();
		while(state_it.hasNext()){
		    FAState state=state_it.next();
		    Iterator<String> sym_it = state.preIt();
		    while(sym_it.hasNext()){
			String sym=sym_it.next();
			Set<FAState> sym_pred=state.getPre(sym);
			fa.trans = fa.trans - prune_bw_set(state, sym, sym_pred, rel);
		    }
		}
	}



// Function to determine the abount of lookahead in simulation.
// Chosen such that computing lookahead simulation can be done in reasonable time (seconds to minutes) on most automata.

	public int lookahead(FiniteAutomaton fa1, FiniteAutomaton fa2){
	    // If fixed lookahead set then use it
	    if(Options.blafixed != 1){
		if(Options.blafixed > 1) return(Options.blafixed);
		else { System.out.println("Wrong fixed lookahead specified! Using 1."); return(1); }
	    }
	    int transitions=fa1.trans+fa2.trans;
	    double x = (double)transitions;
	    x = x/1000;
	    x = Math.log(x)/Math.log(2.0);
	    int y = (int)Math.ceil(x);
	    // Sparse automata get higher lookahead; dense ones get less
	    int sparseness = transitions/(fa1.states.size()+fa2.states.size());
	    int sparseoffset = 4-sparseness;
	    if(sparseoffset < 0) sparseoffset--;
	    int result = 11-y+sparseoffset+Options.blaoffset;
	    // debug("Automata sizes: "+fa1.trans+" + "+fa2.trans+". Sparseoffset: "+sparseoffset+" Lookahead: "+result, 100);
	    if(result >= 1) return result; else return 1;
	}

    // Like lookahead above, but with just one automaton as parameter
	private int single_lookahead(FiniteAutomaton fa1){
	    // If fixed lookahead set then use it
	    if(Options.blafixed != 1){
		if(Options.blafixed > 1) return(Options.blafixed);
		else { System.out.println("Wrong fixed lookahead specified! Using 1."); return(1); }
	    }
	    int transitions=fa1.trans;
	    double x = (double)transitions;
	    x = x/1000;
	    x = Math.log(x)/Math.log(2.0);
	    int y = (int)Math.ceil(x);
	    // Sparse automata get higher lookahead; dense ones get less
	    int sparseness = transitions/(fa1.states.size());
	    int sparseoffset = 4-sparseness;
	    if(sparseoffset < 0) sparseoffset--;
	    int result = 11-y+sparseoffset+Options.blaoffset;
	    if(result >= 1) return result; else return 1;
	}



    // Prune little brothers in fa w.r.t. rel.
    // Additionally little brothers w.r.t. super_rel can be removed if the bigger brother is a transient transition (as given in the last argument).

		public void transient_prune_fw(FiniteAutomaton fa, Set<Pair<FAState,FAState>> rel, Set<Pair<FAState,FAState>> super_rel, Set<Pair<FAState,FAState>> transient_transitions) {
		Iterator<FAState> state_it=fa.states.iterator();
		while(state_it.hasNext()){
		    FAState state=state_it.next();
		    Iterator<String> sym_it = state.nextIt();
		    while(sym_it.hasNext()){
				String sym=sym_it.next();
				Set<FAState> sym_succ=state.getNext(sym);
				    fa.trans = fa.trans - transient_prune_fw_set(state, sym, sym_succ, rel, super_rel, transient_transitions);
		    }
		}
	}


	    private int transient_prune_fw_set(FAState oristate, String sym, Set<FAState> stateset, Set<Pair<FAState,FAState>> rel, Set<Pair<FAState,FAState>> super_rel, Set<Pair<FAState,FAState>> transient_transitions) {
	    Set<FAState> to_remove=new TreeSet<FAState>();
	    Iterator<FAState> it1=stateset.iterator();
	    while(it1.hasNext()){
			FAState state=it1.next();
			Iterator<FAState> it2=stateset.iterator();
	        while(it2.hasNext()){
			    FAState state2=it2.next();
			    if(to_remove.contains(state2)) continue; // removed states cannot kill others
			    if(state==state2) continue; // cannot kill itself
			    if(rel.contains(new Pair<FAState,FAState>(state,state2)) && !rel.contains(new Pair<FAState,FAState>(state2,state))) { 
			    	to_remove.add(state);
				    break; 
				}
			    if(super_rel.contains(new Pair<FAState,FAState>(state,state2)) && transient_transitions.contains(new Pair<FAState,FAState>(oristate,state2))) { 
			    	to_remove.add(state);
				    break;
				}
	        }
	    }
	    if(to_remove.size() >0) 
		{
		    Iterator<FAState> it3=to_remove.iterator();
		    while(it3.hasNext()){
			    FAState state3=it3.next();
			    state3.getPre(sym).remove(oristate);
		    }
		    stateset.removeAll(to_remove);
		}
	    return to_remove.size();
	}


	    // Decompose an automaton into two by a case distinction whether the first transient transition
	    // is taken (case one) or not (case two).

public FiniteAutomaton transient_decomposition_one(FiniteAutomaton fa2){
    FiniteAutomaton fa = removeDead(fa2);
    // make_transient_states_nonacc(fa);
    TreeSet<Pair<FAState,FAState>> t = get_splitting_transient_transitions(fa);
    if(t.isEmpty()) return fa;
    // get the target of the transient transition.
    FAState p = t.first().getRight();
    // find all states reachable from p
    HashSet<FAState> Reachable = new HashSet<FAState>();
    Reachable.add(p);
    while (true) {
			HashSet<FAState> toAdd = new HashSet<FAState>();
			Iterator<FAState> Reachable_it = Reachable.iterator();
			while (Reachable_it.hasNext()) {
				FAState end = Reachable_it.next();
				toAdd.addAll(end.getNext());
			}
			toAdd.removeAll(Reachable);
			if (toAdd.size() == 0)
				break;
			Reachable.addAll(toAdd);
		}
    // States not reachable from p are no longer accepting
    fa.F.retainAll(Reachable);
    return fa;
}

public FiniteAutomaton transient_decomposition_two(FiniteAutomaton fa2){
    FiniteAutomaton fa = removeDead(fa2);
    // make_transient_states_nonacc(fa);
    TreeSet<Pair<FAState,FAState>> t = get_splitting_transient_transitions(fa);
    if(t.isEmpty()) return fa;
    // get the source of the transient transition.
    FAState p = t.first().getLeft();
    // get the target of the transient transition.
    FAState q = t.first().getRight();
    // Now remove all transitions from p to q
    Iterator<String> sym_it = p.nextIt();
    while(sym_it.hasNext()){
	String sym=sym_it.next();
	if(p.getNext(sym).contains(q)){
	    p.getNext(sym).remove(q);
	    q.getPre(sym).remove(p);
	    fa.trans = fa.trans-1;
	}
    }
    return fa;
}





    /* Find all splitting transient transitions in the automaton fa.
       I.e., those such that not all accepting states are reachable from the 
       target of the transient transition. */
    
public TreeSet<Pair<FAState,FAState>> get_splitting_transient_transitions(FiniteAutomaton fa){
ArrayList<FAState> all_states=new ArrayList<FAState>();
HashSet<String> alphabet=new HashSet<String>();
all_states.addAll(fa.states);
alphabet.addAll(fa.alphabet);

int n_states = all_states.size();
int n_symbols = alphabet.size();

FAState[] states = all_states.toArray(new FAState[0]);
ArrayList<String> symbols=new ArrayList<String>(alphabet);

boolean[][] W = new boolean[n_states][n_states];
for(int p=0; p<n_states; p++)
    for(int q=0; q<n_states; q++) W[p][q]=false;

for(int s=0;s<n_symbols;s++){
    String a = symbols.get(s);
    for(int p=0; p<n_states; p++){
	Set<FAState> next = states[p].getNext(a); 
	if (next != null){
	for(int q=0; q<n_states; q++) if(next.contains(states[q])) W[p][q]=true;
	}
    }
}

boolean[][] old_W = new boolean[n_states][n_states];
for(int p=0; p<n_states; p++)
    for(int q=0; q<n_states; q++) old_W[p][q]=W[p][q];

// Compute transitive closure of W
for(int r=0; r< n_states; r++)
	  for(int p=0; p< n_states; p++)
	      if((p != r) && W[p][r]){
		  for(int q=0; q< n_states; q++){
		      if(W[p][q]) continue; // true stays true
		      if(W[r][q]) { W[p][q]=true; }
		  }
	      }

		// Create final result, the transient transitions, as set of pairs of states
		TreeSet<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
			    if(old_W[p][q] && !W[q][p]){ // Can get from p to q, but not every back
				// Now check if all accepting states are reachable from q
				int n=0;
				for(int r=0; r<n_states; r++) if(W[q][r] && fa.F.contains(states[r])) n++; 
				if(n < fa.F.size()) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
			    }
		return FSim2;
}



	    // Find all transient transitions the automaton fa.
public TreeSet<Pair<FAState,FAState>> get_transient_transitions(FiniteAutomaton fa){
ArrayList<FAState> all_states=new ArrayList<FAState>();
HashSet<String> alphabet=new HashSet<String>();
all_states.addAll(fa.states);
alphabet.addAll(fa.alphabet);

int n_states = all_states.size();
int n_symbols = alphabet.size();

FAState[] states = all_states.toArray(new FAState[0]);
ArrayList<String> symbols=new ArrayList<String>(alphabet);

boolean[][] W = new boolean[n_states][n_states];
for(int p=0; p<n_states; p++)
    for(int q=0; q<n_states; q++) W[p][q]=false;

for(int s=0;s<n_symbols;s++){
    String a = symbols.get(s);
    for(int p=0; p<n_states; p++){
	Set<FAState> next = states[p].getNext(a); 
	if (next != null){
	for(int q=0; q<n_states; q++) if(next.contains(states[q])) W[p][q]=true;
	}
    }
}

boolean[][] old_W = new boolean[n_states][n_states];
for(int p=0; p<n_states; p++)
    for(int q=0; q<n_states; q++) old_W[p][q]=W[p][q];

// Compute transitive closure of W
for(int r=0; r< n_states; r++)
	  for(int p=0; p< n_states; p++)
	      if((p != r) && W[p][r]){
		  for(int q=0; q< n_states; q++){
		      if(W[p][q]) continue; // true stays true
		      if(W[r][q]) { W[p][q]=true; }
		  }
	      }

		// Create final result, the transient transitions, as set of pairs of states
		TreeSet<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(old_W[p][q] && !W[q][p]) // Can get from p to q, but not every back
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
}


	    // Find all transient states the automaton fa.
public Set<FAState> get_transient_states(FiniteAutomaton fa){
ArrayList<FAState> all_states=new ArrayList<FAState>();
HashSet<String> alphabet=new HashSet<String>();
all_states.addAll(fa.states);
alphabet.addAll(fa.alphabet);

int n_states = all_states.size();
int n_symbols = alphabet.size();

FAState[] states = all_states.toArray(new FAState[0]);
ArrayList<String> symbols=new ArrayList<String>(alphabet);

boolean[][] W = new boolean[n_states][n_states];
for(int p=0; p<n_states; p++)
    for(int q=0; q<n_states; q++) W[p][q]=false;

for(int s=0;s<n_symbols;s++){
    String a = symbols.get(s);
    for(int p=0; p<n_states; p++){
	Set<FAState> next = states[p].getNext(a); 
	if (next != null){
	for(int q=0; q<n_states; q++) if(next.contains(states[q])) W[p][q]=true;
	}
    }
}

// Compute transitive closure of W
for(int r=0; r< n_states; r++)
	  for(int p=0; p< n_states; p++)
	      if((p != r) && W[p][r]){
		  for(int q=0; q< n_states; q++){
		      if(W[p][q]) continue; // true stays true
		      if(W[r][q]) { W[p][q]=true; }
		  }
	      }

// Create final result
Set<FAState> result = new TreeSet<FAState>();
for(int p=0; p<n_states; p++)	
    if(!W[p][p]) // Cannot get back from p to itself
	result.add(states[p]);

return result;
}



    // Set transient states to non-accepting. Return number of states removed from F
public int make_transient_states_nonacc(FiniteAutomaton fa){

    Set<FAState> ts = get_transient_states(fa);
    int old=fa.F.size();
    fa.F.removeAll(ts);
    return(old-fa.F.size());
}

    // Set transient states to accepting. Return number of states added to F
public int make_transient_states_acc(FiniteAutomaton fa){

    Set<FAState> ts = get_transient_states(fa);
    int old=fa.F.size();
    fa.F.addAll(ts);
    return(fa.F.size()-old);
}



    /* Decomposing the language of automata by keeping only exactly the i-th accepting state 
       of the automaton obtained by removing dead states.
       Returns null iff parameter i out of range. */

public FiniteAutomaton acc_state_decomposition(FiniteAutomaton system2, int i){
	    FiniteAutomaton system=removeDead(system2);
	    if((i<0) || i >= system.F.size()) return null;
	    FAState[] states = system.F.toArray(new FAState[0]);
	    Set<FAState> to_keep=new TreeSet<FAState>();
	    to_keep.add(states[i]);
	    system.F.clear();
	    system.F.addAll(to_keep);
	    return system;
}


    // Author: Richard Mayr.
    // Return a new minimized Buchi automaton, according to the use of lookahead i and the best known techniques.
    // The parameter automaton is not modified.
    // This experimental version adds an extra outer loop to make transient states non-accepting.
    // That seems to help hardly at all.

   public FiniteAutomaton experimental_Minimize_Buchi(FiniteAutomaton system2, int i){
	    FiniteAutomaton system=removeDead(system2);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, drel, bla_frel, bla_brel, bla_drel, jump_drel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r5=0;
		int oldsizes=0;
		int changecounter=0;

		// Extra loop for transient states nonacc
		do{
		// The very outer loop uses transient pruning and jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // Do this until nothing changes anymore. 
		    // No flags used for -rd -de and -q. If only these cause change, then no repeat is needed.
		    do
		    {
			system = removeDead(system);
			drel=sim2.DelayedSimRelNBW(system, null);
			system=quotient(system, drel); 

		        r5 = system.states.size()+system.trans;
			system = single_fwbw_reduce(system);
			r5 = r5 - (system.states.size()+system.trans); // r5 is 0 iff nothing changed		

			brel = sim2.BackwardSimRelNBW(system,null);
			frel = sim2.ForwardSimRelNBW(system, null);
			// Remove transitions in A that are subsumed by other transitions in A
			r1 = removed_trans_extra(system, system, frel, brel);
			// Now remove dead states again
			system = removeDead(system);
		    } while(r1+r5 > 0);

		    oldsizes=system.states.size()+system.trans;

		    // Repeated bw/fw quotienting w.r.t. direct bla sim.
		    system = bla_single_fwbw_reduce(system, i);
		    // system is now also fully bw quotiented.

		    // Prune transitions w.r.t. bla_frel, brel
		    brel = sim2.BackwardSimRelNBW(system,null);
		    bla_frel=sim2.BLASimRelNBW(system, null, i);
		    removed_trans_extra(system, system, bla_frel, brel);
		    system=removeDead(system);
		    
		    // Prune transitions w.r.t. frel, bla_brel
		    // First need to make sure it is fully fw quotiented
		    frel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, frel);
		    // Now compute sims for pruning
		    bla_brel = sim2.BLABSimRelNBW(system, null, i);
		    frel=sim2.ForwardSimRelNBW(system, null);
		    removed_trans_extra(system, system, frel, bla_brel);
		    system=removeDead(system);

		    // Quotienting w.r.t. bla forward delayed simulation 
		    bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
		    system=quotient(system, bla_drel);

		    } while(system.states.size()+system.trans < oldsizes);

		    oldsizes=system.states.size()+system.trans;	
		    
     		    // Separate fw-pruning with transient trans.
		    Set<Pair<FAState,FAState>> transient_transitions = get_transient_transitions(system);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.BLASimRelNBW(system, null, i);
			bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
       		        transient_prune_fw(system, bla_frel, bla_drel, transient_transitions);
			system=removeDead(system);
		    }
		    
		    // Quotient with iterated jumping delayed/bw sim
		    jump_drel = sim2.JumpingDelayedSimRelNBW(system, i);
		    system=quotient(system, jump_drel);
		    
		} while(system.states.size()+system.trans < oldsizes);

  		    changecounter = make_transient_states_nonacc(system);
		
		} while(changecounter >0);

		return system;
	    }


    // -------------- Experimental self-loop decomposition ---------------------


    public FiniteAutomaton Buchi_decompose_selfloops(FiniteAutomaton fa2){
	int decomposed=0; // Counting the actually decomposed loop states
	FiniteAutomaton fa = removeDead(fa2);
	TreeSet<Pair<FAState,FAState>> ttrans = get_transient_transitions(fa);
	ArrayList<FAState> all_states=new ArrayList<FAState>();
	HashSet<String> alphabet=new HashSet<String>();
	all_states.addAll(fa.states);
	alphabet.addAll(fa.alphabet);
	int n_states = all_states.size();
	int n_symbols = alphabet.size();
	FAState[] states = all_states.toArray(new FAState[0]);
	ArrayList<String> symbols=new ArrayList<String>(alphabet);
	Set<FAState> loopstates=new TreeSet<FAState>();
	// First find all states with selfloops
	for(int s=0;s<n_symbols;s++){
	    String a = symbols.get(s);
	    for(int p=0; p<n_states; p++){
		if(states[p].getNext(a) != null){
		    // initial state is not decomposed
		    if(states[p].getNext(a).contains(states[p]) && (states[p] != fa.getInitialState())) loopstates.add(states[p]);
		}
	    }
	}
	// System.out.println("Decompose_selfloops: Treating "+loopstates.size()+" selfloops.");
	if(loopstates.size()==0) return fa;
	// Now iterate over all loopstates
	Iterator<FAState> it = loopstates.iterator();
	boolean flag=false;
	while(it.hasNext()){
	    flag=false;
	    FAState state=it.next();
	    for(int s=0;s<n_symbols;s++){
		String a = symbols.get(s);
		if(state.getNext(a)==null) continue;
		Iterator<FAState> it2 = state.getNext(a).iterator();
		while(it2.hasNext()){
		    FAState state2 = it2.next();
		    if(state2 == state) continue; // self-loop does not count here
		    // Create a copy newstate of state and make it accepting if state is
		    flag=true;
		    FAState newstate = fa.createState();
		    if(fa.F.contains(state)){
			if(!ttrans.contains(new Pair<FAState,FAState>(state,state2))) fa.F.add(newstate);
			// else System.out.println("Decompose_selfloops: Copy state denied acc status.");
		    }
		    fa.addTransition(newstate, state2, a); // unique exit transition for newstate, except selfloop
		    // give newstate the same selfloops as state
		    for(int s2=0;s2<n_symbols;s2++){
			String a2 = symbols.get(s2);
			if(state.getNext(a2) != null){
			    if(state.getNext(a2).contains(state)) fa.addTransition(newstate, newstate, a2);
			}
		    }
		    // from all predecessors of state, add transition to newstate
		    for(int s2=0;s2<n_symbols;s2++){
			String a2 = symbols.get(s2);	
			if(state.getPre(a2)==null) continue;
			Iterator<FAState> it3 = state.getPre(a2).iterator();
			while(it3.hasNext()){
			    FAState prestate = it3.next();
			    if(prestate != state) fa.addTransition(prestate, newstate, a2);
			}
		    }
		}
	    }
	    if(flag) decomposed++; 

	    // delete non-loop transitions from original state
	    for(int s2=0;s2<n_symbols;s2++){
		String a2 = symbols.get(s2);
		if(state.getNext(a2) == null) continue;
		Iterator<FAState> it4 = state.getNext(a2).iterator();
		Set<FAState> toRemove=new TreeSet<FAState>();
		while(it4.hasNext()){
		    FAState poststate = it4.next();
		    if(poststate==state) continue;
		    poststate.getPre(a2).remove(state);
		    toRemove.add(poststate);
		}
		state.getNext(a2).removeAll(toRemove);
	    }

	}
	// System.out.println("Decompose_selfloops: Actually decomposed "+decomposed+" selfloops.");
	return fa;
    }


    public int num_selfloops(FiniteAutomaton fa){
	int result=0;
	ArrayList<FAState> all_states=new ArrayList<FAState>();
	HashSet<String> alphabet=new HashSet<String>();
	all_states.addAll(fa.states);
	alphabet.addAll(fa.alphabet);

	int n_states = all_states.size();
	int n_symbols = alphabet.size();

	FAState[] states = all_states.toArray(new FAState[0]);
	ArrayList<String> symbols=new ArrayList<String>(alphabet);

	for(int s=0;s<n_symbols;s++){
	    String a = symbols.get(s);
	    for(int p=0; p<n_states; p++){
		if(states[p].getNext(a) != null){
		    if(states[p].getNext(a).contains(states[p])) result++;
		}
	    }
	}
	return result;
    }


    public int num_acc_selfloops(FiniteAutomaton fa){
	int result=0;
	ArrayList<FAState> all_states=new ArrayList<FAState>();
	HashSet<String> alphabet=new HashSet<String>();
	all_states.addAll(fa.states);
	alphabet.addAll(fa.alphabet);

	int n_states = all_states.size();
	int n_symbols = alphabet.size();

	FAState[] states = all_states.toArray(new FAState[0]);
	ArrayList<String> symbols=new ArrayList<String>(alphabet);

	for(int s=0;s<n_symbols;s++){
	    String a = symbols.get(s);
	    for(int p=0; p<n_states; p++){
		if(states[p].getNext(a) != null){
		    if(states[p].getNext(a).contains(states[p]) && fa.F.contains(states[p])) result++;
		}
	    }
	}
	return result;
    }



    //--------------------------------------------------------------------

  public FiniteAutomaton experimental_noj_Minimize_Buchi(FiniteAutomaton system2, int i){
	    FiniteAutomaton system=removeDead(system2);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, drel, bla_frel, bla_brel, bla_drel, jump_drel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses transient pruning and jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // Do this until nothing changes anymore. 
		    // No flags used for -rd -de and -q. If only these cause change, then no repeat is needed.
		    do
		    {
			system = removeDead(system);
			drel=sim2.DelayedSimRelNBW(system, null);
			system=quotient(system, drel); 

		        r5 = system.states.size()+system.trans;
			system = single_fwbw_reduce(system);
			r5 = r5 - (system.states.size()+system.trans); // r5 is 0 iff nothing changed		

			brel = sim2.BackwardSimRelNBW(system,null);
			frel = sim2.ForwardSimRelNBW(system, null);
			// Remove transitions in A that are subsumed by other transitions in A
			r1 = removed_trans_extra(system, system, frel, brel);
			// Now remove dead states again
			system = removeDead(system);
		    } while(r1+r5 > 0);

		    oldsizes=system.states.size()+system.trans;

		    // Repeated bw/fw quotienting w.r.t. direct bla sim.
		    system = bla_single_fwbw_reduce(system, i);
		    // system is now also fully bw quotiented.

		    // Prune transitions w.r.t. bla_frel, brel
		    brel = sim2.BackwardSimRelNBW(system,null);
		    bla_frel=sim2.BLASimRelNBW(system, null, i);
		    removed_trans_extra(system, system, bla_frel, brel);
		    system=removeDead(system);
		    
		    // Prune transitions w.r.t. frel, bla_brel
		    // First need to make sure it is fully fw quotiented
		    frel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, frel);
		    // Now compute sims for pruning
		    bla_brel = sim2.BLABSimRelNBW(system, null, i);
		    frel=sim2.ForwardSimRelNBW(system, null);
		    removed_trans_extra(system, system, frel, bla_brel);
		    system=removeDead(system);

		    // Quotienting w.r.t. bla forward delayed simulation 
		    bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
		    system=quotient(system, bla_drel);

		    } while(system.states.size()+system.trans < oldsizes);

		    oldsizes=system.states.size()+system.trans;	

    		    // Separate fw-pruning with transient trans.
		    Set<Pair<FAState,FAState>> transient_transitions = get_transient_transitions(system);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.BLASimRelNBW(system, null, i);
			bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
       		        transient_prune_fw(system, bla_frel, bla_drel, transient_transitions);
			system=removeDead(system);
		    }
		    
		    // Quotient with iterated jumping delayed/bw sim
		    /* This is removed in the NOJ version
		    jump_drel = sim2.JumpingDelayedSimRelNBW(system, i);
		    system=quotient(system, jump_drel);
		    */
		    
		    } while(system.states.size()+system.trans < oldsizes);

		return system;
	    }



    // Author: Richard Mayr.
    // Return a new minimized Buchi automaton. Just remove dead states and quotient w.r.t. delayed simulation.
    // The parameter automaton is not modified.

    public FiniteAutomaton LightweightMinimize_Buchi(FiniteAutomaton system2, int la){
	    FiniteAutomaton system=removeDead(system2);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_drel;
	    if(la==1) bla_drel=sim2.DelayedSimRelNBW(system, null);
	    else bla_drel=sim2.BLADelayedSimRelNBW(system, null, la);
	    system=quotient(system, bla_drel);

	    return system;
   }


    // Author: Richard Mayr.
    // Return a new minimized Buchi automaton, according to the use of lookahead i and the best known techniques.
    // The parameter automaton is not modified.

   public FiniteAutomaton Minimize_Buchi(FiniteAutomaton system2, int i){
	    FiniteAutomaton system=removeDead(system2);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, drel, bla_frel, bla_brel, bla_drel, jump_drel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses transient pruning and jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // Do this until nothing changes anymore. 
		    // No flags used for -rd -de and -q. If only these cause change, then no repeat is needed.
		    do
		    {
			system = removeDead(system);
			drel=sim2.DelayedSimRelNBW(system, null);
			system=quotient(system, drel); 

		        r5 = system.states.size()+system.trans;
			system = single_fwbw_reduce(system);
			r5 = r5 - (system.states.size()+system.trans); // r5 is 0 iff nothing changed		

			brel = sim2.BackwardSimRelNBW(system,null);
			frel = sim2.ForwardSimRelNBW(system, null);
			// Remove transitions in A that are subsumed by other transitions in A
			r1 = removed_trans_extra(system, system, frel, brel);
			// Now remove dead states again
			system = removeDead(system);
		    } while(r1+r5 > 0);

		    oldsizes=system.states.size()+system.trans;

		    // Repeated bw/fw quotienting w.r.t. direct bla sim.
		    system = bla_single_fwbw_reduce(system, i);
		    // system is now also fully bw quotiented.

		    // Prune transitions w.r.t. bla_frel, brel
		    brel = sim2.BackwardSimRelNBW(system,null);
		    bla_frel=sim2.BLASimRelNBW(system, null, i);
		    removed_trans_extra(system, system, bla_frel, brel);
		    system=removeDead(system);
		    
		    // Prune transitions w.r.t. frel, bla_brel
		    // First need to make sure it is fully fw quotiented
		    frel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, frel);
		    // Now compute sims for pruning
		    bla_brel = sim2.BLABSimRelNBW(system, null, i);
		    frel=sim2.ForwardSimRelNBW(system, null);
		    removed_trans_extra(system, system, frel, bla_brel);
		    system=removeDead(system);

		    // Quotienting w.r.t. bla forward delayed simulation 
		    bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
		    system=quotient(system, bla_drel);

		    } while(system.states.size()+system.trans < oldsizes);

		    oldsizes=system.states.size()+system.trans;	

    		    // Separate fw-pruning with transient trans.
		    Set<Pair<FAState,FAState>> transient_transitions = get_transient_transitions(system);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.BLASimRelNBW(system, null, i);
			bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
       		        transient_prune_fw(system, bla_frel, bla_drel, transient_transitions);
			system=removeDead(system);
		    }
		    
		    // Quotient with iterated jumping delayed/bw sim
		    jump_drel = sim2.JumpingDelayedSimRelNBW(system, i);
		    system=quotient(system, jump_drel);
		    
		    } while(system.states.size()+system.trans < oldsizes);

		return system;
	    }


    //---------------------------------------------------------------------------------------------


    // Author: Richard Mayr.
    // Return a new minimized Buchi automaton, according to the use of lookahead i and the best known techniques.
    // The parameter automaton is not modified.
    // This is the same as Minimize_Buchi, except that 2-pebble enhanced forward lookahead direct sim is used instead of 1-pebble.

   public FiniteAutomaton addpebble_Minimize_Buchi(FiniteAutomaton system2, int i){
	    FiniteAutomaton system=removeDead(system2);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, drel, bla_frel, bla_brel, bla_drel, jump_drel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses transient pruning and jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // Do this until nothing changes anymore. 
		    // No flags used for -rd -de and -q. If only these cause change, then no repeat is needed.
		    do
		    {
			system = removeDead(system);
			drel=sim2.DelayedSimRelNBW(system, null);
			system=quotient(system, drel); 

		        r5 = system.states.size()+system.trans;
			system = single_fwbw_reduce(system);
			r5 = r5 - (system.states.size()+system.trans); // r5 is 0 iff nothing changed		

			brel = sim2.BackwardSimRelNBW(system,null);
			frel = sim2.ForwardSimRelNBW(system, null);
			// Remove transitions in A that are subsumed by other transitions in A
			r1 = removed_trans_extra(system, system, frel, brel);
			// Now remove dead states again
			system = removeDead(system);
		    } while(r1+r5 > 0);

		    oldsizes=system.states.size()+system.trans;

		    // Repeated bw/fw quotienting w.r.t. direct bla sim.
		    system = addpebble_bla_single_fwbw_reduce(system, i);
		    // system is now also fully bw quotiented.

		    // Prune transitions w.r.t. bla_frel, brel
		    brel = sim2.BackwardSimRelNBW(system,null);
		    bla_frel=sim2.addpebble_BLASimRelNBW(system, null, i);
		    removed_trans_extra(system, system, bla_frel, brel);
		    system=removeDead(system);
		    
		    // Prune transitions w.r.t. frel, bla_brel
		    // First need to make sure it is fully fw quotiented
		    frel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, frel);
		    // Now compute sims for pruning
		    bla_brel = sim2.BLABSimRelNBW(system, null, i);
		    frel=sim2.ForwardSimRelNBW(system, null);
		    removed_trans_extra(system, system, frel, bla_brel);
		    system=removeDead(system);

		    // Quotienting w.r.t. bla forward delayed simulation 
		    bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
		    system=quotient(system, bla_drel);

		    } while(system.states.size()+system.trans < oldsizes);

		    oldsizes=system.states.size()+system.trans;	

    		    // Separate fw-pruning with transient trans.
		    Set<Pair<FAState,FAState>> transient_transitions = get_transient_transitions(system);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.addpebble_BLASimRelNBW(system, null, i);
			bla_drel=sim2.BLADelayedSimRelNBW(system, null, i);
       		        transient_prune_fw(system, bla_frel, bla_drel, transient_transitions);
			system=removeDead(system);
		    }
		    
		    // Quotient with iterated jumping delayed/bw sim
		    jump_drel = sim2.JumpingDelayedSimRelNBW(system, i);
		    system=quotient(system, jump_drel);
		    
		    } while(system.states.size()+system.trans < oldsizes);

		return system;
	    }


    private FiniteAutomaton addpebble_bla_single_fwbw_reduce(FiniteAutomaton system, int i){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	    oldsys=system.states.size();
	    oldsys_trans = system.trans;

	    bla_frel=sim2.addpebble_BLASimRelNBW(system, null, i);
	    prune_fw(system, bla_frel);
            system=quotient(system, bla_frel);
	    system=removeDead(system);
	
   	    bla_brel = sim2.BLABSimRelNBW(system, null, i);
            prune_bw(system, bla_brel);
            system=quotient(system, bla_brel);
	    system=removeDead(system);
	 } while(oldsys > system.states.size() || oldsys_trans > system.trans);
    return(system);
    }


    //-------------------------------------------------------------------------------


    // Author: Richard Mayr.
    // Return a new minimized Buchi automaton, according to the use of lookahead i and the best known techniques.
    // The parameter automaton is not modified.
    // It uses 2-pebble sim., repeated transitive closure delayed sim., and transient pruning with lookahead fair sim.

   public FiniteAutomaton besteffort_Minimize_Buchi(FiniteAutomaton system2, int i){
	    FiniteAutomaton system=removeDead(system2);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, drel, bla_frel, bla_brel, bla_drel, jump_drel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses transient pruning and jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // Do this until nothing changes anymore. 
		    // No flags used for -rd -de and -q. If only these cause change, then no repeat is needed.
		    do
		    {
			system = removeDead(system);
			drel=sim2.DelayedSimRelNBW(system, null);
			system=quotient(system, drel); 

		        r5 = system.states.size()+system.trans;
			system = single_fwbw_reduce(system);
			r5 = r5 - (system.states.size()+system.trans); // r5 is 0 iff nothing changed		

			brel = sim2.BackwardSimRelNBW(system,null);
			frel = sim2.ForwardSimRelNBW(system, null);
			// Remove transitions in A that are subsumed by other transitions in A
			r1 = removed_trans_extra(system, system, frel, brel);
			// Now remove dead states again
			system = removeDead(system);
		    } while(r1+r5 > 0);

		    oldsizes=system.states.size()+system.trans;

		    // Repeated bw/fw quotienting w.r.t. direct bla sim.
		    system = addpebble_bla_single_fwbw_reduce(system, i);
		    // system is now also fully bw quotiented.

		    // Prune transitions w.r.t. bla_frel, brel
		    brel = sim2.BackwardSimRelNBW(system,null);
		    bla_frel=sim2.addpebble_BLASimRelNBW(system, null, i);
		    removed_trans_extra(system, system, bla_frel, brel);
		    system=removeDead(system);
		    
		    // Prune transitions w.r.t. frel, bla_brel
		    // First need to make sure it is fully fw quotiented
		    frel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, frel);
		    // Now compute sims for pruning
		    bla_brel = sim2.BLABSimRelNBW(system, null, i);
		    frel=sim2.ForwardSimRelNBW(system, null);
		    removed_trans_extra(system, system, frel, bla_brel);
		    system=removeDead(system);

		    // Quotienting w.r.t. bla forward delayed simulation 
		    bla_drel=sim2.rep_BLADelayedSimRelNBW(system, null, i);
		    system=quotient(system, bla_drel);

		    } while(system.states.size()+system.trans < oldsizes);

		    oldsizes=system.states.size()+system.trans;	

    		    // Separate fw-pruning with transient trans.
		    Set<Pair<FAState,FAState>> transient_transitions = get_transient_transitions(system);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.addpebble_BLASimRelNBW(system, null, i);
			bla_drel=sim2.BLAFairSimRelNBW(system, null, i);
       		        transient_prune_fw(system, bla_frel, bla_drel, transient_transitions);
			system=removeDead(system);
		    }
		    
		    // Quotient with iterated jumping delayed/bw sim
		    jump_drel = sim2.JumpingDelayedSimRelNBW(system, i);
		    system=quotient(system, jump_drel);
		    
		    } while(system.states.size()+system.trans < oldsizes);

		return system;
	    }



    //-----------------------------------------------------------------------------------------------

	private FiniteAutomaton single_fwbw_reduce(FiniteAutomaton system){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel,brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	     oldsys=system.states.size();
	     oldsys_trans = system.trans;

	     frel = sim2.ForwardSimRelNBW(system,null);
	     prune_fw(system,frel);
             system=quotient(system, frel);
	     system=removeDead(system);
	
   	     brel = sim2.BackwardSimRelNBW(system,null);
             prune_bw(system,brel);
             system=quotient(system, brel);
	     system=removeDead(system);
	     } while(oldsys > system.states.size() || oldsys_trans > system.trans);

	    return(system);
	}	


    private FiniteAutomaton bla_single_fwbw_reduce(FiniteAutomaton system, int i){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	    oldsys=system.states.size();
	    oldsys_trans = system.trans;

	    bla_frel=sim2.BLASimRelNBW(system, null, i);
	    prune_fw(system, bla_frel);
            system=quotient(system, bla_frel);
	    system=removeDead(system);
	
   	    bla_brel = sim2.BLABSimRelNBW(system, null, i);
            prune_bw(system, bla_brel);
            system=quotient(system, bla_brel);
	    system=removeDead(system);
	 } while(oldsys > system.states.size() || oldsys_trans > system.trans);
    return(system);
    }

    // Like bla_single_fwbw_reduce, except bw first
    private FiniteAutomaton bla_single_bwfw_reduce(FiniteAutomaton system, int i){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	    oldsys=system.states.size();
	    oldsys_trans = system.trans;

   	    bla_brel = sim2.BLABSimRelNBW(system, null, i);
            prune_bw(system, bla_brel);
            system=quotient(system, bla_brel);
	    system=removeDead(system);

	    bla_frel=sim2.BLASimRelNBW(system, null, i);
	    prune_fw(system, bla_frel);
            system=quotient(system, bla_frel);
	    system=removeDead(system);
	 } while(oldsys > system.states.size() || oldsys_trans > system.trans);
    return(system);
    }

	

   // Preprocess two Buchi automata for later later inclusion checking.
   // Modifies both arguments. Languages are not preserved, but the inclusion/noninclusion between them is preserved.
   // Acts differently, depending on specified options.
   // Returns true if inclusion is found to hold already during the preprocessing, otherwise false (i.e., false means `don't know').

   public AutomatonPreprocessingResult Preprocess_Buchi(FiniteAutomaton system, FiniteAutomaton spec){
       	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, drel, bla_frel, bla_brel, bla_drel, jump_drel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r2=0;
		int r3=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses transient pruning and jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // The inner loop appies reductions without lookahead
		    do
		    {
			if(Options.rd){
			    system = removeDead(system);
			    spec = removeDead(spec);
			    /*
			    debug("Aut A (dead states removed): # of Trans. "
					+ system.trans + ", # of States " + system.states.size()
					+ ".",100);
			    debug("Aut B (dead states removed): # of Trans. "
					+ spec.trans + ", # of States " + spec.states.size() + ".",100);
			    */
			}
			// showprogress("rd", system, spec);
			if(Options.delayed){
			    drel=sim2.DelayedSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, drel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    system=quotient(system, drel); 
			    spec=quotient(spec, drel);
			    /*
			    debug("Aut A (delayed quotiented): # of Trans. "
					+ system.trans + ", # of States " + system.states.size()
					+ ".",100);
			    debug("Aut B (delayed quotiented): # of Trans. "
					+ spec.trans + ", # of States " + spec.states.size() + ".",100);
			    */
			}
			else if(Options.quotient && !Options.qr){ // Both -de and -qr superseed -q
			    frel = sim2.ForwardSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    system = quotient(system, frel);
			    spec = quotient(spec, frel);
			}

			if(Options.qr){
			    r5 = system.states.size()+system.trans+spec.states.size()+spec.trans;
			    AutomatonPreprocessingResult x = combined_fwbw_reduce(system, spec);
			    if(x.result) return x; else { system=x.system; spec=x.spec; }
			    r5 = r5 - (system.states.size()+system.trans+spec.states.size()+spec.trans); 
			    /*
			    debug("Aut A after qr minimization: # of Trans. "
					+ system.trans + ", # of States " + system.states.size()
					+ ".",100);
					debug("Aut B after qr minimization: # of Trans. "
					+ spec.trans + ", # of States " + spec.states.size() + ".",100);
			    */
			    // r5 is 0 iff nothing changed
			}

			// Superpruning:
			// These optimizations are only correct if the automata are fully quotiented,
			// no little brothers, no dead states
			if(Options.backward && Options.qr && Options.rd && Options.superpruning){
			    frel = sim2.ForwardSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    brel = sim2.BackwardSimRelNBW(system, spec);
			    if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    // Remove transitions in system that are subsumed by other transitions in system
			    r1 = removed_trans_extra(system, system, frel, brel);
			    r1 += removed_trans_extra(spec, spec, frel, brel);
			    // Now remove dead states again
			    system = removeDead(system);
			    spec = removeDead(spec);
			}

			// Now comes the non-language-preserving part of superpruning
			if(Options.backward && Options.qr && Options.rd && Options.superpruning && Options.C1){
			    // First prune transitions in system that cannot be used in counterexamples to inclusion
			    if(Options.delayed){
				drel=sim2.DelayedSimRelNBW(system, spec);
				if(know_inclusion(system, spec, drel)) return(new AutomatonPreprocessingResult(system, spec, true));
				brel=sim2.acceptance_blind_BackwardSimRelNBW(system, spec);
				// This brel cannot witness Buchi incl. (unlike for NFA) since it is acceptance blind bw sim.
				r2 = removed_trans_extra(system, spec, drel, brel);
			    }
			    else{
				frel=sim2.ForwardSimRelNBW(system, spec);
				if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
				brel=sim2.acceptance_blind_BackwardSimRelNBW(system, spec);
				// This brel cannot witness Buchi incl. (unlike for NFA) since it is acceptance blind bw sim.
				r2 = removed_trans_extra(system, spec, frel, brel);
			    }
			    // Remove dead states again
			    system = removeDead(system);
			    spec = removeDead(spec);
			    // Now apply product pruning
			    // Remove states/transitions from spec that are unreachable in the product of system and spec. These are not needed.
			    r3 = product_pruning(system, spec);
			}
		    } while(r1+r2+r3+r5 > 0);

		    // Remember the sizes to detect if anything changes.
		    oldsizes=system.states.size()+system.trans+spec.states.size()+spec.trans;

    		    // This outer loop uses lookahead simulation
		    if(Options.blamin){
			// Repeated fw/bw quotienting and pruning w.r.t. direct bla sim.
			if(Options.qr){
			    AutomatonPreprocessingResult x = bla_combined_fwbw_reduce(system, spec);
			    if(x.result) return x; else { system=x.system; spec=x.spec; }
			    // system/spec are now also fully bw quotiented.
			}
			// Superpruning:
			// These optimizations are only correct if the automata are fully quotiented,
			// no little brothers, no dead states
			if(Options.backward && Options.qr && Options.rd && Options.superpruning){
			    // Prune transitions w.r.t. bla_frel, brel
			    bla_frel=sim2.BLASimRelNBW(system, spec, lookahead(system, spec));
			    if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    brel = sim2.BackwardSimRelNBW(system, spec);
			    if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
		    	    removed_trans_extra(system, system, bla_frel, brel);
			    removed_trans_extra(spec, spec, bla_frel, brel);
			    system=removeDead(system);
			    spec=removeDead(spec);
			    // Prune transitions w.r.t. frel, bla_brel
			    // First need to make sure it is fully fw quotiented
			    frel=sim2.ForwardSimRelNBW(system, spec);
			    system=quotient(system, frel);
			    spec=quotient(spec, frel);
			    // Now compute sims for pruning
			    bla_brel = sim2.BLABSimRelNBW(system, spec, lookahead(system, spec));
			    if(know_inclusion_bw(system, spec, bla_brel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    frel=sim2.ForwardSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    removed_trans_extra(system, system, frel, bla_brel);
			    removed_trans_extra(spec, spec, frel, bla_brel);
			    system=removeDead(system);
			    spec=removeDead(spec);
			}

			// Now comes the non-language-preserving part of superpruning
			if(Options.backward && Options.qr && Options.rd && Options.superpruning && Options.C1){
			    // First prune transitions in system that cannot be used in counterexamples to inclusion
			    if(Options.delayed){
				bla_drel=sim2.BLADelayedSimRelNBW(system, spec, lookahead(system,spec));
				if(know_inclusion(system, spec, bla_drel)) return(new AutomatonPreprocessingResult(system, spec, true));
				brel=sim2.weak_BLABSimRelNBW(system, spec, lookahead(system,spec));
				// This brel cannot witness Buchi incl. (unlike for NFA) since it is acceptance blind bw sim.
				removed_trans_extra(system, spec, bla_drel, brel);
			    }
			    else{
				bla_frel=sim2.BLASimRelNBW(system, spec, lookahead(system, spec));
				if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
				brel=sim2.weak_BLABSimRelNBW(system, spec, lookahead(system,spec));
				// This brel cannot witness Buchi incl. (unlike for NFA) since it is acceptance blind bw sim.
				removed_trans_extra(system, spec, bla_frel, brel);
			    }
			    // Remove dead states again
			    system = removeDead(system);
			    spec = removeDead(spec);
			    // Now apply product pruning
			    // Remove states/transitions from spec that are unreachable in the product of system and spec. These are not needed.
			    product_pruning(system, spec);
			    // Remove dead states again
			    system = removeDead(system);
			    spec = removeDead(spec);
			}

			// Quotienting w.r.t. bla forward delayed simulation 
			if(Options.delayed){
			    bla_drel=sim2.BLADelayedSimRelNBW(system, spec, lookahead(system,spec));
			    if(know_inclusion(system, spec, bla_drel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    system=quotient(system, bla_drel);
			    spec=quotient(spec, bla_drel);
			}
		    }
		    } while(system.states.size()+system.trans+spec.states.size()+spec.trans < oldsizes);

		    oldsizes=system.states.size()+system.trans+spec.states.size()+spec.trans;	

    		    // Separate fw-pruning with transient transitions
		    if(Options.transient_pruning){
		    Set<Pair<FAState,FAState>> transient_transitions = get_transient_transitions(system);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.BLASimRelNBW(system, null, single_lookahead(system));
			bla_drel=sim2.BLADelayedSimRelNBW(system, null, single_lookahead(system));
       		        transient_prune_fw(system, bla_frel, bla_drel, transient_transitions);
			system=removeDead(system);
		    }
		    transient_transitions = get_transient_transitions(spec);
		    if(transient_transitions.size() >0){
			bla_frel=sim2.BLASimRelNBW(spec, null, single_lookahead(spec));
			bla_drel=sim2.BLADelayedSimRelNBW(spec, null, single_lookahead(spec));
       		        transient_prune_fw(spec, bla_frel, bla_drel, transient_transitions);
			spec=removeDead(spec);
		    }
		    }
		    
		    // Quotient with iterated jumping delayed/bw sim
		    if(Options.jumpsim_quotienting){
			jump_drel = sim2.JumpingDelayedSimRelNBW(system, single_lookahead(system));
			system=quotient(system, jump_drel);
			jump_drel = sim2.JumpingDelayedSimRelNBW(spec, single_lookahead(spec));
			spec=quotient(spec, jump_drel);
		    }
		    
		    } while(system.states.size()+system.trans+spec.states.size()+spec.trans < oldsizes);

		return(new AutomatonPreprocessingResult(system, spec, false));
	    }



   // Lightweight version of Preprocess two Buchi automata for later inclusion checking.
   // Only removes dead states and quotients w.r.t. delayed (or direct) simulation.
   // Modifies both arguments. Languages are not preserved, but the inclusion/noninclusion between them is preserved.
   // Acts differently, depending on specified options.
   // Returns true if inclusion is found to hold already during the preprocessing, otherwise false (i.e., false means `don't know').

   public AutomatonPreprocessingResult Lightweight_Preprocess_Buchi(FiniteAutomaton system, FiniteAutomaton spec){
       	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, drel;
	    if(Options.rd){
		system = removeDead(system);
		spec = removeDead(spec);
	    }
	    if(Options.delayed){
		drel=sim2.DelayedSimRelNBW(system, spec);
		if(know_inclusion(system, spec, drel)) return(new AutomatonPreprocessingResult(system, spec, true));
		system=quotient(system, drel); 
		spec=quotient(spec, drel);
		return(new AutomatonPreprocessingResult(system, spec, false));
	    }
	    else if(Options.quotient || Options.qr){ // Both -de and -qr superseed -q
		frel = sim2.ForwardSimRelNBW(system, spec);
		if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
		system = quotient(system, frel);
		spec = quotient(spec, frel);
		return(new AutomatonPreprocessingResult(system, spec, false));
	    }
	    else return(new AutomatonPreprocessingResult(system, spec, false));
}
   
   public AutomatonPreprocessingResult Lightweight_Preprocess_Buchi2(FiniteAutomaton system, FiniteAutomaton spec){
       Simulation sim2 = new Simulation();
   Set<Pair<FAState, FAState>> frel, drel;
   system = removeDead(system);
   spec = removeDead(spec);
   
   frel = sim2.ForwardSimRelNBW(system, spec);
   if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
   system = quotient(system, frel);
   spec = quotient(spec, frel);
   
   drel=sim2.DelayedSimRelNBW(system, spec);
   if(know_inclusion(system, spec, drel)) return(new AutomatonPreprocessingResult(system, spec, true));
   system=quotient(system, drel); 
   spec=quotient(spec, drel);
   return(new AutomatonPreprocessingResult(system, spec, false));
  }



    // Checks if the forward relation rel already implies inclusion between system and spec
    public boolean know_inclusion(FiniteAutomaton system, FiniteAutomaton spec, Set<Pair<FAState, FAState>> rel){
	if (Options.C1 && rel.contains(new Pair<FAState, FAState>(system.getInitialState(), spec.getInitialState())))
	    return true; 
	else return false;
    }


    // Checks if the backward relation rel already implies inclusion between system and spec
    private boolean know_inclusion_bw(FiniteAutomaton system, FiniteAutomaton spec, Set<Pair<FAState, FAState>> rel){
	if(!Options.C1) return false;

	//System.out.println("Checking bw incl. witness");
	Iterator<FAState> sys_F_it = system.F.iterator();
	while(sys_F_it.hasNext()){
	    FAState sys_F = sys_F_it.next();
	    Iterator<FAState> spec_F_it = spec.F.iterator();
	    boolean found=false;
	    while(spec_F_it.hasNext()){
		FAState spec_F = spec_F_it.next();
		if (rel.contains(new Pair<FAState, FAState>(sys_F, spec_F))) found=true;
	    }
	    if(!found) { /* System.out.println("Checking bw incl. witness done: FALSE"); */ return false; }
	}
	// System.out.println("Checking bw incl. witness done: TRUE");
	return true;
    }



    private AutomatonPreprocessingResult combined_fwbw_reduce(FiniteAutomaton system, FiniteAutomaton spec){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel,brel;
	    int oldsizes=0;
	    do{
             oldsizes=system.states.size()+spec.states.size()+system.trans+spec.trans;
	     frel = sim2.ForwardSimRelNBW(system, spec);
	     if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
	     prune_fw(system,frel);
	     prune_fw(spec, frel);
             system=quotient(system, frel);
	     spec=quotient(spec, frel);
	     if(Options.rd){
		 system=removeDead(system);
		 spec=removeDead(spec);
	     }
   	     brel = sim2.BackwardSimRelNBW(system, spec);
	     if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
             prune_bw(system,brel);
	     prune_bw(spec, brel);
             system=quotient(system, brel);
	     spec=quotient(spec, brel);
	     if(Options.rd){
		 system=removeDead(system);
		 spec=removeDead(spec);
	     }
	     } while(oldsizes > system.states.size()+spec.states.size()+system.trans+spec.trans);

	    return(new AutomatonPreprocessingResult(system, spec, false));
	}	


    private AutomatonPreprocessingResult bla_combined_fwbw_reduce(FiniteAutomaton system, FiniteAutomaton spec){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsizes=0;
	    do{
             oldsizes=system.states.size()+spec.states.size()+system.trans+spec.trans;
	     bla_frel = sim2.BLASimRelNBW(system, spec, lookahead(system,spec));
	     if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
	     prune_fw(system, bla_frel);
	     prune_fw(spec, bla_frel);
             system=quotient(system, bla_frel);
	     spec=quotient(spec, bla_frel);
	     if(Options.rd){
		 system=removeDead(system);
		 spec=removeDead(spec);
	     }
   	     bla_brel = sim2.BLABSimRelNBW(system, spec, lookahead(system,spec));
	     if(know_inclusion_bw(system, spec, bla_brel)) return(new AutomatonPreprocessingResult(system, spec, true));
             prune_bw(system, bla_brel);
	     prune_bw(spec, bla_brel);
             system=quotient(system, bla_brel);
	     spec=quotient(spec, bla_brel);
	     if(Options.rd){
		 system=removeDead(system);
		 spec=removeDead(spec);
	     }
	     } while(oldsizes > system.states.size()+spec.states.size()+system.trans+spec.trans);

	    return(new AutomatonPreprocessingResult(system, spec, false));
	}	


    // Just used for debugging
    private void showprogress(String s, FiniteAutomaton aut1, FiniteAutomaton aut2){
	System.out.println(s);
	System.out.println("Aut A: # of Trans. "+aut1.trans+", # of States "+aut1.states.size()+".");
	System.out.println("Aut B: # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
    }


    // ------------------ Minimization of Finite Automata -----------------------------------------


    // Author: Richard Mayr.
    // Return a new minimized finite automaton. Just remove dead states and quotient w.r.t. lookahead simulation.
    // The parameter automaton is not modified.

    public FiniteAutomaton LightweightMinimize_Finite(FiniteAutomaton system2, int la){
	    FiniteAutomaton system=finite_removeDead(system2);

	    boolean addempty = system.F.contains(system.getInitialState()); // empty word in language
	    system = FiniteOneAcc(system);
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> rel;
	    if(la==1) rel = sim2.ForwardSimRelNBW(system, null); 
	    else rel = sim2.BLASimRelNBW(system, null, la);
	    system=quotient(system, rel);

	    // re-add the empty word if needed, and then minimize some more.
	    if(addempty){
		    system = addemptyword(system);
		    system = finite_removeDead(system);
		    rel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, rel);
	    }
	    return system;
   }

    // Author: Richard Mayr.
    // Return a new minimized finite automaton (not Buchi aut.!), 
    // according to the use of lookahead i and the best known techniques.
    // The parameter automaton is not modified.

    public FiniteAutomaton Minimize_Finite(FiniteAutomaton system2, int i, boolean oneacc, boolean usejump, boolean usepebble){
	    FiniteAutomaton system=finite_removeDead(system2);
	    
	    boolean addempty = system.F.contains(system.getInitialState()); // empty word in language
	    // Preprocess system to have only one acc state. This removes the empty word from the
	    // language. Thus one might need to add it again at the end. 
	    if(oneacc) system = FiniteOneAcc(system);

	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, bla_frel, bla_brel, jrel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // Do this until nothing changes anymore. 
		    do
		    {
			system = finite_removeDead(system);

		        r5 = system.states.size()+system.trans;
			system = finite_single_fwbw_reduce(system);
			r5 = r5 - (system.states.size()+system.trans); // r5 is 0 iff nothing changed		

			brel = sim2.BackwardSimRelNBW(system,null);
			frel = sim2.ForwardSimRelNBW(system, null);
			// Remove transitions in A that are subsumed by other transitions in A
			r1 = removed_trans_extra(system, system, frel, brel);
			// Now remove dead states again
			system = finite_removeDead(system);
		    } while(r1+r5 > 0);

		    oldsizes=system.states.size()+system.trans;

		    // Repeated bw/fw quotienting w.r.t. direct bla sim.
		    system = finite_bla_single_fwbw_reduce(system, i);
		    // system is now also fully bw quotiented.

		    // Prune transitions w.r.t. bla_frel, brel
		    brel = sim2.BackwardSimRelNBW(system,null);
		    bla_frel=sim2.BLASimRelNBW(system, null, i);
		    removed_trans_extra(system, system, bla_frel, brel);
		    system=finite_removeDead(system);
		    
		    // Prune transitions w.r.t. frel, bla_brel
		    // First need to make sure it is fully fw quotiented
		    frel=sim2.ForwardSimRelNBW(system, null);
		    system=quotient(system, frel);
		    // Now compute sims for pruning
		    bla_brel = sim2.BLABSimRelNBW(system, null, i);
		    frel=sim2.ForwardSimRelNBW(system, null);
		    removed_trans_extra(system, system, frel, bla_brel);
		    system=finite_removeDead(system);

		    // Quotienting w.r.t. bla forward simulation 
		    bla_frel=sim2.BLASimRelNBW(system, null, i);
		    system=quotient(system, bla_frel);

		    } while(system.states.size()+system.trans < oldsizes);

		// quotient with iterated jumping direct sim.
		oldsizes=system.states.size()+system.trans;

		if(usejump){
		jrel = sim2.JumpingDirectSimRelNBW(system, i);
		system=quotient(system, jrel);
		}
		
		if(usepebble){
		    int extra_oldsizes=system.states.size()+system.trans; 
		    // System.out.println("Computing addpebble.");
		    bla_frel = sim2.addpebble_BLASimRelNBW(system, null, i);
		    prune_fw(system, bla_frel);
		    system=quotient(system, bla_frel);
		    system=finite_removeDead(system);
		    /*
		    if(system.states.size()+system.trans < extra_oldsizes) 
			System.out.println("Pebble success: "+extra_oldsizes+" to "+(system.states.size()+system.trans));
		    else System.out.println("Pebble gave nothing extra here.");
		    */
		}

		} while(system.states.size()+system.trans < oldsizes);

		// re-add the empty word if needed, and then minimize some more.
		if(oneacc && addempty){
		    // Check if system is almost universal, i.e., just lacking the empty word
		    // so that adding the empty word again would make it universal.
		    if(finite_almost_universal(system)){
			// Create new one-state universal automaton
			FiniteAutomaton univ_system = new FiniteAutomaton();
			univ_system.name = system.name;
			univ_system.setInitialState(univ_system.createState());
			univ_system.F.add(univ_system.getInitialState());
			Iterator<String> sym_it = system.alphabet.iterator();
			while(sym_it.hasNext()){
			    String sym=sym_it.next();
			    univ_system.addTransition(univ_system.getInitialState(), univ_system.getInitialState(), sym);
			}
			return univ_system;
		    }
		    else{
			system = addemptyword(system);
			system = finite_removeDead(system);
			frel=sim2.ForwardSimRelNBW(system, null);
			system=quotient(system, frel);
		    }
		}
		// Last check if aut really got smaller, or larger due to the oneacc transform 
		if(system.states.size() < system2.states.size()) return system;
		if((system.states.size() == system2.states.size()) && (system.trans < system2.trans)) return system; 
		return system2;
	    }

    // Check if a finite aut. has a particular form, that makes it almost universal,
    // i.e., just lacking the empty word.
    private boolean finite_almost_universal(FiniteAutomaton system){
	if(system.states.size()==2 && system.F.size()==1 && !system.F.contains(system.getInitialState())){
	    Iterator<FAState> F_it = system.F.iterator();
	    FAState finstate = F_it.next();
	    Iterator<String> sym_it = system.alphabet.iterator();
	    while(sym_it.hasNext()){
		String sym=sym_it.next();
		if(finstate.getNext(sym) != null){
		    if(finstate.getNext(sym).size() != 0) return false;
		}
		if(!system.getInitialState().getNext(sym).containsAll(system.states)) return false;
	    }
	    return true;
	}
	else return false;
    }


	private FiniteAutomaton finite_single_fwbw_reduce(FiniteAutomaton system){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel,brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	     oldsys=system.states.size();
	     oldsys_trans = system.trans;

	     frel = sim2.ForwardSimRelNBW(system,null);
	     prune_fw(system,frel);
             system=quotient(system, frel);
	     system=finite_removeDead(system);
	
   	     brel = sim2.BackwardSimRelNBW(system,null);
             prune_bw(system,brel);
             system=quotient(system, brel);
	     system=finite_removeDead(system);
	     } while(oldsys > system.states.size() || oldsys_trans > system.trans);

	    return(system);
	}	


    private FiniteAutomaton finite_bla_single_fwbw_reduce(FiniteAutomaton system, int i){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	    oldsys=system.states.size();
	    oldsys_trans = system.trans;

	    bla_frel=sim2.BLASimRelNBW(system, null, i);
	    prune_fw(system, bla_frel);
            system=quotient(system, bla_frel);
	    system=finite_removeDead(system);
	
   	    bla_brel = sim2.BLABSimRelNBW(system, null, i);
            prune_bw(system, bla_brel);
            system=quotient(system, bla_brel);
	    system=finite_removeDead(system);
	 } while(oldsys > system.states.size() || oldsys_trans > system.trans);
    return(system);
    }


    // Like finite_bla_single_fwbw_reduce, except that bw comes first.
    private FiniteAutomaton finite_bla_single_bwfw_reduce(FiniteAutomaton system, int i){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsys=0;
	    int oldsys_trans=0;
	    do{
	    oldsys=system.states.size();
	    oldsys_trans = system.trans;

	    // System.out.println("BWFW before prune: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
   	    bla_brel = sim2.BLABSimRelNBW(system, null, i);
	    // System.out.println("BWFW Size of bw rel: "+bla_brel.size());
            prune_bw(system, bla_brel);
	    // System.out.println("BWFW after prune: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
            system=quotient(system, bla_brel);
	    system=finite_removeDead(system);

	    bla_frel=sim2.BLASimRelNBW(system, null, i);
	    prune_fw(system, bla_frel);
            system=quotient(system, bla_frel);
	    system=finite_removeDead(system);
	 } while(oldsys > system.states.size() || oldsys_trans > system.trans);
    return(system);
    }


    /* Change a finite automaton s.t. it has only one accepting state.
     The finite-word language remains the same (but not the Buchi language),
     except that the empty word is removed from the language.
     The empty word might have to be re-added later.
     It creates a new accepting state acc and for every transition x-a->y where y is accepting
     we add a transition x-a->acc.
     Finally only acc stays accepting.
     The argument is modified and returned as result.
    */
    public FiniteAutomaton FiniteOneAcc(FiniteAutomaton system){
		FAState acc = system.createState();
		Iterator<FAState> it=system.F.iterator();
		while(it.hasNext()){
		    FAState state=it.next();
		    Iterator<String> sym_it = state.preIt();
		    while(sym_it.hasNext()){
			String sym=sym_it.next();
			Set<FAState> sym_pred=state.getPre(sym);
			Iterator<FAState> it2=sym_pred.iterator();
			while(it2.hasNext()){
			    FAState state2=it2.next();
			    system.addTransition(state2, acc, sym);
			}
		    }
		}
		system.F.clear();
		system.F.add(acc);
		// Previous accepting states with no outgoing transitions will have turned dead
		system = finite_removeDead(system);

    return(system);
    }


   /* Change a finite automaton s.t. to add the empty word to its language.
     The argument is modified the returned as result.
    */
    private FiniteAutomaton addemptyword(FiniteAutomaton system){
		FAState newstart = system.createState();
		FAState state = system.getInitialState();
		Iterator<String> sym_it = state.nextIt();
		    while(sym_it.hasNext()){
			String sym=sym_it.next();
			Set<FAState> sym_post=state.getNext(sym);
			Iterator<FAState> it2=sym_post.iterator();
			while(it2.hasNext()){
			    FAState state2=it2.next();
			    system.addTransition(newstart, state2, sym);
			}
		    }
    system.setInitialState(newstart);
    system.F.add(newstart);
    
    return(system);
    }



    //----------- Proprocessing of finite automata for inclusion checking -----------------------------------

   // Lightweight version of Preprocess two finite automata for later inclusion checking.
   // Transforms into oneacc form, removes dead states and quotients w.r.t. direct simulation.
   // Modifies both arguments. Languages are not preserved, but the inclusion/noninclusion between them is preserved.
   // Returns true if inclusion is found to hold already during the preprocessing, otherwise false (i.e., false means `don't know').

   public AutomatonPreprocessingResult Lightweight_Preprocess_Finite(FiniteAutomaton system, FiniteAutomaton spec){
       	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, drel;

		frel = sim2.ForwardSimRelNBW(system, spec);
		if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
		system = quotient(system, frel);
		spec = quotient(spec, frel);
		return(new AutomatonPreprocessingResult(system, spec, false));
   }

   /* 
   Like Preprocess_Buchi, but for finite-word automata. 
   Obviously no delayed/fair simulation is used here.
   It is highly recommended to use Oneacc to transform the aut into a form with just one accepting state first.
   This method uses finite_removeDead, since remove_Dead is incorrect for finite word aut.
   Returns true if inclusion is found to hold already during the preprocessing, otherwise false (i.e., false means `don't know'),
   and the minimized automata.
   */

   public AutomatonPreprocessingResult Preprocess_Finite(FiniteAutomaton system, FiniteAutomaton spec){

       	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel, brel, bla_frel, bla_brel, jumprel;
	    // These count the number of removed transitions, or reduced states.
	        int r1=0;
		int r2=0;
		int r3=0;
		int r5=0;
		int oldsizes=0;

		// The very outer loop uses jumping sim. quotienting.
		do{
		// The outer loop uses expensive lookahead pruning and quotienting at the end, if options given.
		do{
		    // The inner loop appies reductions without lookahead
		    do
		    {
			if(Options.rd){
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			    /*
			    debug("Aut A (dead states removed): # of Trans. "
					+ system.trans + ", # of States " + system.states.size()
					+ ".",100);
			    debug("Aut B (dead states removed): # of Trans. "
					+ spec.trans + ", # of States " + spec.states.size() + ".",100);
			    */
			}
			// showprogress("rd", system, spec);
			if(Options.quotient && !Options.qr){ // Both -de and -qr superseed -q
			    frel = sim2.ForwardSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    system = quotient(system, frel);
			    spec = quotient(spec, frel);
			}
			else if(Options.qr){
			    r5 = system.states.size()+system.trans+spec.states.size()+spec.trans;
			    AutomatonPreprocessingResult x = finite_combined_fwbw_reduce(system, spec);
			    if(x.result) return x; else { system=x.system; spec=x.spec; }
			    r5 = r5 - (system.states.size()+system.trans+spec.states.size()+spec.trans); 
			    /*
			    debug("Aut A after qr minimization: # of Trans. "
					+ system.trans + ", # of States " + system.states.size()
					+ ".",100);
					debug("Aut B after qr minimization: # of Trans. "
					+ spec.trans + ", # of States " + spec.states.size() + ".",100);
			    */
			    // r5 is 0 iff nothing changed
			}

			// Superpruning:
			// These optimizations are only correct if the automata are fully quotiented,
			// no little brothers, no dead states
			if(Options.backward && Options.qr && Options.rd && Options.superpruning){
			    frel = sim2.ForwardSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    brel = sim2.BackwardSimRelNBW(system, spec);
			    if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    // Remove transitions in system that are subsumed by other transitions in system
			    r1 = removed_trans_extra(system, system, frel, brel);
			    r1 += removed_trans_extra(spec, spec, frel, brel);
			    // Now remove dead states again
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			}

			// Now comes the non-language-preserving part of superpruning
			if(Options.backward && Options.qr && Options.rd && Options.superpruning && Options.C1){
			    // First prune transitions in system that cannot be used in counterexamples to inclusion
				frel=sim2.ForwardSimRelNBW(system, spec);
				if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
				brel=sim2.acceptance_blind_BackwardSimRelNBW(system, spec);
				if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
				r2 = removed_trans_extra(system, spec, frel, brel);
			    // Remove dead states again
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			    // Now apply product pruning
			    // Remove states/transitions from spec that are unreachable in the product of system and spec. These are not needed.
			    r3 = product_pruning(system, spec);
			}
		    } while(r1+r2+r3+r5 > 0);

		    // Remember the sizes to detect if anything changes.
		    oldsizes=system.states.size()+system.trans+spec.states.size()+spec.trans;

    		    // This outer loop uses lookahead simulation
		    if(Options.blamin){
			// Repeated fw/bw quotienting and pruning w.r.t. direct bla sim.
			if(Options.qr){
			    AutomatonPreprocessingResult x = finite_bla_combined_fwbw_reduce(system, spec);
			    if(x.result) return x; else { system=x.system; spec=x.spec; }
			    // system/spec are now also fully bw quotiented.
			}
			// Superpruning:
			// These optimizations are only correct if the automata are fully quotiented,
			// no little brothers, no dead states
			if(Options.backward && Options.qr && Options.rd && Options.superpruning){
			    // Prune transitions w.r.t. bla_frel, brel
			    bla_frel=sim2.BLASimRelNBW(system, spec, lookahead(system, spec));
			    if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    brel = sim2.BackwardSimRelNBW(system, spec);
			    if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
		    	    removed_trans_extra(system, system, bla_frel, brel);
			    removed_trans_extra(spec, spec, bla_frel, brel);
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			    // Prune transitions w.r.t. frel, bla_brel
			    // First need to make sure it is fully fw quotiented
			    frel=sim2.ForwardSimRelNBW(system, spec);
			    system=quotient(system, frel);
			    spec=quotient(spec, frel);
			    // Now compute sims for pruning
			    bla_brel = sim2.BLABSimRelNBW(system, spec, lookahead(system, spec));
			    if(know_inclusion_bw(system, spec, bla_brel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    frel=sim2.ForwardSimRelNBW(system, spec);
			    if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    removed_trans_extra(system, system, frel, bla_brel);
			    removed_trans_extra(spec, spec, frel, bla_brel);
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			}

			// Now comes the non-language-preserving part of superpruning
			if(Options.backward && Options.qr && Options.rd && Options.superpruning && Options.C1){
			    // First prune transitions in system that cannot be used in counterexamples to inclusion
				bla_frel=sim2.BLASimRelNBW(system, spec, lookahead(system, spec));
				if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
				brel=sim2.weak_BLABSimRelNBW(system, spec, lookahead(system,spec));
				if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
				removed_trans_extra(system, spec, bla_frel, brel);
			    // Remove dead states again
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			    // Now apply product pruning
			    // Remove states/transitions from spec that are unreachable in the product of system and spec. These are not needed.
			    product_pruning(system, spec);
			    // Remove dead states again
			    system = finite_removeDead(system);
			    spec = finite_removeDead(spec);
			}

			// Quotienting w.r.t. bla forward direct simulation 
			    bla_frel=sim2.BLASimRelNBW(system, spec, lookahead(system, spec));
			    if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
			    system = quotient(system, bla_frel);
			    spec = quotient(spec, bla_frel);

		    }
		    } while(system.states.size()+system.trans+spec.states.size()+spec.trans < oldsizes);

		oldsizes=system.states.size()+system.trans+spec.states.size()+spec.trans;
		// Quotient with iterated jumping delayed/bw sim
		// It must be done separately for each aut. Doing it combined is incorrect.
		    if(Options.jumpsim_quotienting){
			jumprel = sim2.JumpingDirectSimRelNBW(system, single_lookahead(system));
			system=quotient(system, jumprel);
			jumprel = sim2.JumpingDirectSimRelNBW(spec, single_lookahead(spec));
			spec=quotient(spec, jumprel);
		    }
		} while(system.states.size()+system.trans+spec.states.size()+spec.trans < oldsizes);

		return(new AutomatonPreprocessingResult(system, spec, false));
	    }



    private AutomatonPreprocessingResult finite_combined_fwbw_reduce(FiniteAutomaton system, FiniteAutomaton spec){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> frel,brel;
	    int oldsizes=0;
	    do{
             oldsizes=system.states.size()+spec.states.size()+system.trans+spec.trans;
	     frel = sim2.ForwardSimRelNBW(system, spec);
	     if(know_inclusion(system, spec, frel)) return(new AutomatonPreprocessingResult(system, spec, true));
	     prune_fw(system,frel);
	     prune_fw(spec, frel);
             system=quotient(system, frel);
	     spec=quotient(spec, frel);
	     if(Options.rd){
		 system=finite_removeDead(system);
		 spec=finite_removeDead(spec);
	     }
   	     brel = sim2.BackwardSimRelNBW(system, spec);
	     if(know_inclusion_bw(system, spec, brel)) return(new AutomatonPreprocessingResult(system, spec, true));
             prune_bw(system,brel);
	     prune_bw(spec, brel);
             system=quotient(system, brel);
	     spec=quotient(spec, brel);
	     if(Options.rd){
		 system=finite_removeDead(system);
		 spec=finite_removeDead(spec);
	     }
	     } while(oldsizes > system.states.size()+spec.states.size()+system.trans+spec.trans);

	    return(new AutomatonPreprocessingResult(system, spec, false));
	}	


    private AutomatonPreprocessingResult finite_bla_combined_fwbw_reduce(FiniteAutomaton system, FiniteAutomaton spec){
	    Simulation sim2 = new Simulation();
	    Set<Pair<FAState, FAState>> bla_frel, bla_brel;
	    int oldsizes=0;
	    do{
             oldsizes=system.states.size()+spec.states.size()+system.trans+spec.trans;
	     bla_frel = sim2.BLASimRelNBW(system, spec, lookahead(system,spec));
	     if(know_inclusion(system, spec, bla_frel)) return(new AutomatonPreprocessingResult(system, spec, true));
	     prune_fw(system, bla_frel);
	     prune_fw(spec, bla_frel);
             system=quotient(system, bla_frel);
	     spec=quotient(spec, bla_frel);
	     if(Options.rd){
		 system=finite_removeDead(system);
		 spec=finite_removeDead(spec);
	     }
   	     bla_brel = sim2.BLABSimRelNBW(system, spec, lookahead(system,spec));
	     if(know_inclusion_bw(system, spec, bla_brel)) return(new AutomatonPreprocessingResult(system, spec, true));
             prune_bw(system, bla_brel);
	     prune_bw(spec, bla_brel);
             system=quotient(system, bla_brel);
	     spec=quotient(spec, bla_brel);
	     if(Options.rd){
		 system=finite_removeDead(system);
		 spec=finite_removeDead(spec);
	     }
	     } while(oldsizes > system.states.size()+spec.states.size()+system.trans+spec.trans);

	    return(new AutomatonPreprocessingResult(system, spec, false));
	}	




    // ---------------------------------------------------------------------------------------------
    // Extended minimization with adding transitions, i.e., saturation


   public FiniteAutomaton saturate_Minimize_Finite(FiniteAutomaton system2, int i){
       FiniteAutomaton best_system = Minimize_Finite(system2, i, true, true, false);
       FiniteAutomaton system = finite_removeDead(best_system);
       // best_system is a fallback copy of the best aut. encountered so far, in case adding transitions only makes things worse.

       Simulation sim2 = new Simulation();
       Set<Pair<FAState, FAState>> bla_frel, bla_brel;
       int nstates = 0;
       int ntrans = 0;
       boolean changed = true;

       int num_fw=0;
       int num_bw=0;

       while(changed){
	   // System.out.println("satNFA init: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   nstates = system.states.size();
	   ntrans = system.trans;

	   bla_frel = sim2.BLASimRelNBW(system, null, i);
	   num_fw = saturate_transitions(system, reverse_rel(bla_frel), bla_frel);

	   // System.out.println("satNFA drelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   system = quotient(system, bla_brel);

	   // System.out.println("satNFA bquotient: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   num_bw = saturate_transitions(system, bla_brel, reverse_rel(bla_brel));

	   // System.out.println("satNFA brelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   // If fw did something, then prune with bwfw first.
	   // Otherwise, the fw added transition are immediately removed by fwbw pruning.
	   if(num_fw >0){
	       // System.out.println("Try bwfw.");
	       system = finite_bla_single_bwfw_reduce(system, i);
	       // System.out.println("satNFA after bwfw: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   }

   	   system = Minimize_Finite(system, i, false, true, false); // Don't use oneacc again. Once is enough, done above.
	   // Did things get "better" ? If so, continue.
	   changed = (system.states.size() < nstates) || ((system.states.size() == nstates) && (system.trans < ntrans));
	   // If nothing better, then keep the old best system and return that.
	   if(changed) best_system = finite_removeDead(system);

	   // System.out.println("satNFA minimized again: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
       }
       return best_system;
   }



    public FiniteAutomaton saturate_Minimize_Buchi(FiniteAutomaton system2, int i){
       FiniteAutomaton best_system = Minimize_Buchi(system2, i);
       FiniteAutomaton system = removeDead(best_system);
       // fallback_system is a fallback copy, in case adding transitions only makes things worse.
       
       Simulation sim2 = new Simulation();
       Set<Pair<FAState, FAState>> bla_drel, bla_brel;
       int nstates = 0;
       int ntrans = 0;
       boolean changed = true;
       int num_fw=0;
       int num_bw=0;

       while(changed){
	   // System.out.println("satBuchi init: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   nstates = system.states.size();
	   ntrans = system.trans;

	   bla_drel = sim2.BLADelayedSimRelNBW(system, null, i);
	   num_fw = saturate_transitions(system, reverse_rel(bla_drel), bla_drel);

	   // System.out.println("satBuchi drelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   system = quotient(system, bla_brel);

	   // System.out.println("satBuchi bquotient: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   num_bw = saturate_transitions(system, bla_brel, reverse_rel(bla_brel));

	   // System.out.println("satBuchi brelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   // If fw did something, then prune with bwfw first.
	   // Otherwise, the fw added transition are immediately removed by fwbw pruning.
	   if(num_fw >0){
	       // System.out.println("Try bwfw.");
	       system = bla_single_bwfw_reduce(system, i);
	       // System.out.println("satNFA after bwfw: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   }

   	   system = Minimize_Buchi(system, i);
	   // Did things get "better" ? If so, continue.
	   changed = (system.states.size() < nstates) || ((system.states.size() == nstates) && (system.trans < ntrans));
	   if(changed) best_system = removeDead(system);

	   // System.out.println("satBuchi minimized again: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
       }
       return best_system;
   }




    private int saturate_transitions(FiniteAutomaton system, Set<Pair<FAState, FAState>> srel, Set<Pair<FAState, FAState>> trel){
	int number_added=0;

	Set<Pair<FAState,FAState>> toadd = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
	Iterator<String> sym_it = system.getAllTransitionSymbols().iterator();
	while(sym_it.hasNext()){
	    String sym=sym_it.next();
	    toadd.clear();
	    Iterator<FAState> s_it = system.states.iterator();
	    while(s_it.hasNext()){
		FAState s = s_it.next();
		Set<FAState> above_s = get_above(system, s, srel);
		Iterator<FAState> t_it = system.states.iterator();
		while(t_it.hasNext()){
		    FAState t = t_it.next();
		    if(addable_transition(above_s,sym,t,trel)) toadd.add(new Pair<FAState, FAState>(s,t));
		}
	    }
	    Iterator<Pair<FAState,FAState>> toadd_it = toadd.iterator();
	    while(toadd_it.hasNext()){
		Pair<FAState,FAState> pair = toadd_it.next();
		system.addTransition(pair.getLeft(), pair.getRight(), sym);
		++number_added;
	    }
	}
	return number_added;
    }

    private Set<FAState> get_above(FiniteAutomaton system, FAState s, Set<Pair<FAState,FAState>> srel){
	Set<FAState> result = new TreeSet<FAState>(new StateComparator());
	Iterator<FAState> it = system.states.iterator();
	while(it.hasNext()){
	    FAState b = it.next();
	    if(srel.contains(new Pair<FAState, FAState>(s, b))) result.add(b);
	}
	return result;
    }


    private boolean addable_transition(Set<FAState> above_s, String sym, FAState t, Set<Pair<FAState, FAState>> trel){
	Iterator<FAState> it = above_s.iterator();
	while(it.hasNext()){
	    FAState b = it.next();
	    if(b.getNext(sym)==null) continue;
	    Iterator<FAState> it2 = b.getNext(sym).iterator();
	    while(it2.hasNext()){
		FAState b2 = it2.next();
		// b2 must be trel bigger than t
		if(trel.contains(new Pair<FAState, FAState>(t, b2))) return true;
	    }
	}
	return false;
    }


    private Set<Pair<FAState,FAState>> reverse_rel(Set<Pair<FAState, FAState>> rel){
	Set<Pair<FAState,FAState>> result = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
	Iterator<Pair<FAState,FAState>> it = rel.iterator();
	while(it.hasNext()){
	    Pair<FAState,FAState> pair = it.next();
	    result.add(new Pair<FAState, FAState>(pair.getRight(),pair.getLeft()));
	}
	return result;
    }
    


    // SAT2: More aggressive version of saturation method. Keep going until no change (in size).

    public FiniteAutomaton sat2_Minimize_Buchi(FiniteAutomaton system2, int i){
       FiniteAutomaton best_system = Minimize_Buchi(system2, i);
       FiniteAutomaton system = removeDead(best_system);
              
       Simulation sim2 = new Simulation();
       Set<Pair<FAState, FAState>> bla_drel, bla_brel;

       int nstates = 0;
       int ntrans = 0;
       int maxit = 10; // At most 10 iterations with no change in the number of states 
       int[] pasttrans = new int[maxit];
       int counter=0;
       boolean changed = true;
       int num_fw=0;
       int num_bw=0;

       while(changed && counter<maxit){
	   changed=false;
	   // System.out.println("satBuchi init: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   nstates = system.states.size();
	   ntrans = system.trans;

	   bla_drel = sim2.BLADelayedSimRelNBW(system, null, i);
	   num_fw = saturate_transitions(system, reverse_rel(bla_drel), bla_drel);

	   // System.out.println("satBuchi drelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   system = quotient(system, bla_brel);

	   // System.out.println("satBuchi bquotient: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   num_bw = saturate_transitions(system, bla_brel, reverse_rel(bla_brel));

	   // System.out.println("satBuchi brelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   // If fw did something, then prune with bwfw first.
	   // Otherwise, the fw added transition are immediately removed by fwbw pruning.
	   if(num_fw >0){
	       // System.out.println("Try bwfw.");
	       system = bla_single_bwfw_reduce(system, i);
	       // System.out.println("satNFA after bwfw: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   }

   	   system = Minimize_Buchi(system, i);

	   pasttrans[counter++] = system.trans;
	   // Did things get "different" ? If so, continue.
	   if((system.states.size() < nstates) || (system.trans < best_system.trans)){
	       changed=true;
	       counter=0;  // reset counter
	       best_system = removeDead(system);
	   } else{  // number of states stayed the same
	       changed=true; // continue unless same number of transitions seen in the past.
	       for(int j=0; j<counter-1; j++) if(system.trans == pasttrans[j]) changed=false;
	   }

	   // System.out.println("sat2_Buchi minimized again: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
       }
       return best_system;
   }



    public FiniteAutomaton sat2_Minimize_Finite(FiniteAutomaton system2, int i){
       FiniteAutomaton best_system = Minimize_Finite(system2, i, true, true, false);
       FiniteAutomaton system = finite_removeDead(best_system);
              
       Simulation sim2 = new Simulation();
       Set<Pair<FAState, FAState>> bla_frel, bla_brel;

       int nstates = 0;
       int ntrans = 0;
       int maxit = 10; // At most 10 iterations with no change in the number of states 
       int[] pasttrans = new int[maxit];
       int counter=0;
       boolean changed = true;
       int num_fw=0;
       int num_bw=0;

       while(changed && counter<maxit){
	   changed=false;
	   // System.out.println("satBuchi init: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   nstates = system.states.size();
	   ntrans = system.trans;

	   bla_frel = sim2.BLASimRelNBW(system, null, i);
	   num_fw = saturate_transitions(system, reverse_rel(bla_frel), bla_frel);

	   // System.out.println("satBuchi drelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   system = quotient(system, bla_brel);

	   // System.out.println("satBuchi bquotient: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   bla_brel = sim2.BLABSimRelNBW(system, null, i);
	   num_bw = saturate_transitions(system, bla_brel, reverse_rel(bla_brel));
	   // System.out.println("satBuchi brelsat: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");

	   // If fw did something, then prune with bwfw first.
	   // Otherwise, the fw added transition are immediately removed by fwbw pruning.
	   if(num_fw >0){
	       // System.out.println("Try bwfw.");
	       system = finite_bla_single_bwfw_reduce(system, i);
	       // System.out.println("satNFA after bwfw: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
	   }

   	   system = Minimize_Finite(system, i, false, true, false); // Don't use oneacc again. Once is enough, done above.

	   pasttrans[counter++] = system.trans;
	   // Did things get "different" ? If so, continue.
	   if((system.states.size() < nstates) || (system.trans < best_system.trans)){
	       changed=true;
	       counter=0;  // reset counter
	       best_system = finite_removeDead(system);
	   } else{  // number of states stayed the same
	       changed=true; // continue unless same number of transitions seen in the past.
	       for(int j=0; j<counter-1; j++) if(system.trans == pasttrans[j]) changed=false;
	   }

	   // System.out.println("sat2_Finite minimized again: Aut A: # of Trans. "+system.trans+", # of States "+system.states.size()+".");
       }
       return best_system;
   }


// End of class
}


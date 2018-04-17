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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeMap;

import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.Pair;


public class ProductBuilder {
	
	
	public static FiniteAutomaton build(FiniteAutomaton automaton
			, List<String> prefix, List<String> suffix) {
		
		FiniteAutomaton product = new FiniteAutomaton();
		// for omega word, every letter is a state
		// u,v 0- u[0] -> 1 -u[1]-> 2-> ... - u[n]-> n+1 - v[0]-> n+2... n+k+1 - v[k] -> n+1     
		// we have a loop here
		AutomatonWord wordAut = new AutomatonWord(prefix, suffix);
		// initialization
		FAState proInit = product.createState();
		Map<IntPair, FAState> proMap=new HashMap<IntPair, FAState>();
		
		FAState autInit = automaton.getInitialState();
		IntPair initPair = new IntPair(autInit.id, wordAut.getInitState(), wordAut.getNumStates());
		Map<Integer, FAState> autMap = new TreeMap<>();
		proMap.put(initPair, proInit);
		autMap.put(autInit.id, autInit);
		product.setInitialState(proInit);
		
		if(testAcceptance(automaton, wordAut, wordAut.getInitState(), autInit)) {
			product.F.add(proInit);
		}
		
		Queue<IntPair> queue = new LinkedList<>();
		queue.add(initPair);
		
		while(! queue.isEmpty()) {
			IntPair statePair = queue.poll();
			FAState stateAut = autMap.get(statePair.getLeft());
			String label = wordAut.getNextLabel(statePair.getRight());
			Set<FAState> succs = stateAut.getNext(label);
			FAState statePro = proMap.get(statePair);
			if(succs == null) continue;
			for(FAState succ : succs) {
				
				int nextState = wordAut.getNextState(statePair.getRight());
				IntPair newPair = new IntPair(succ.id, nextState, wordAut.getNumStates());
				FAState stateSucc = proMap.get(newPair);
				if(stateSucc == null) {
					stateSucc = product.createState();
					queue.add(newPair);
					proMap.put(newPair, stateSucc);
				}
				product.addTransition(statePro, stateSucc, label);
				if(testAcceptance(automaton, wordAut, nextState, succ)) {
					product.F.add(stateSucc);
				}
				autMap.put(succ.id, succ);
			}
		}
		
		return product;
	}
	
	
	private static boolean testAcceptance(
			FiniteAutomaton automaton, AutomatonWord wordAut, int state, FAState autState) {
		if(automaton.F.contains(autState) 
		&& wordAut.isAccepted(state)) {
			return true;
		}
		return false;
	}
	
	// every state in b has only one transition
	public static FiniteAutomaton build(FiniteAutomaton a, FiniteAutomaton b) {
		FiniteAutomaton c = new FiniteAutomaton();
		// for omega word, every letter is a state

		// initialization
		FAState cInit = c.createState();
		c.setInitialState(cInit);
		Map<Integer, FAState> cMap = new HashMap<Integer, FAState>();
		
		FAState aInit = a.getInitialState();
		FAState bInit = b.getInitialState();
		
		int cId = getStateId(aInit.id, bInit.id, b.states.size());

		Map<Integer, FAState> aMap = new HashMap<>();
		Map<Integer, FAState> bMap = new HashMap<>();
		cMap.put(cId, cInit);


		for(FAState s : a.states) {
			aMap.put(s.id, s);
		}
		
		for(FAState s : b.states) {
			bMap.put(s.id, s);
		}
		
		if(a.F.contains(aInit) && b.F.contains(bInit)) {
			c.F.add(cInit);
		}
		
		Queue<Pair<Integer, Integer>> queue = new LinkedList<>();
		queue.add(new Pair<>(aInit.id, bInit.id));
		
		while(! queue.isEmpty()) {
			Pair<Integer, Integer> statePair = queue.poll();
			FAState aState = aMap.get(statePair.getLeft());
			FAState bState = bMap.get(statePair.getRight());
			String label = bState.nextIt().next();
			Set<FAState> succs = aState.getNext(label);
			
			if(succs == null) continue;
			cId = getStateId(statePair.getLeft(), statePair.getRight(), b.states.size());
			FAState cState = cMap.get(cId);
			
			for(FAState aSucc : succs) {
				FAState bSucc = bState.getNext(label).iterator().next();
				Pair<Integer, Integer> newPair = new Pair<Integer, Integer>(aSucc.id, bSucc.id);
				cId = getStateId(aSucc.id, bSucc.id, b.states.size());
				FAState stateSucc = cMap.get(cId);
				if(stateSucc == null) {
					stateSucc = c.createState();
					queue.add(newPair);
					cMap.put(cId, stateSucc);
				}
				c.addTransition(cState, stateSucc, label);
				if(a.F.contains(aSucc) && b.F.contains(bSucc)) {
					c.F.add(stateSucc);
				}
			}
		}
		
		return c;
	}
	
	private static int getStateId(int f, int d, int n) {
		return f * n + d;
	}

}

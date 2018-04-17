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

import java.util.Iterator;
import java.util.List;
import java.util.Stack;
import java.util.TreeMap;

import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.Pair;

/**
 * @author liyong
 * Adapted from SCC.java to check emptiness of a Buechi automaton
 * */
public class EmptinessCheck {
	
	int index = 0;
	Stack<FAState> S = new Stack<FAState>();
	FiniteAutomaton fa;
	TreeMap<Integer,Integer> v_index = new TreeMap<Integer,Integer>();
	TreeMap<Integer,Integer> v_lowlink = new TreeMap<Integer,Integer>();
	private FAState f = null;
	
	public EmptinessCheck(FiniteAutomaton fa){
		this.fa=fa;
	}
	
	public boolean isEmpty() {
		Iterator<FAState> st_it=fa.F.iterator();
		// needs to guarantee that all final states are reachable
		while(st_it.hasNext()){
			FAState st=st_it.next();
			if(!v_index.containsKey(st.id)){
				if(tarjan(st))
					return false;
			}
		}
		return true;
	}
	
	public boolean getShortestCycle() {
		Iterator<FAState> st_it=fa.F.iterator();
		// needs to guarantee that all final states are reachable
		while(st_it.hasNext()){
			FAState st=st_it.next();
			if(!v_index.containsKey(st.id)){
				if(tarjan(st))
					return false;
			}
		}
		return true;
	}

	
	boolean tarjan(FAState v) {
		v_index.put(v.id, index);
		v_lowlink.put(v.id, index);
		index++;
		S.push(v);
		Iterator<String> next_it=v.nextIt();
		while(next_it.hasNext()){
			String next=next_it.next();
			Iterator<FAState> st_it=v.getNext(next).iterator();
			while(st_it.hasNext()){
				FAState v_prime=st_it.next();
				if(!v_index.containsKey(v_prime.id)){
					if(tarjan(v_prime)) return true;
					v_lowlink.put(v.id,	Math.min(v_lowlink.get(v.id), v_lowlink.get(v_prime.id)));
				}else if(S.contains(v_prime)){
					v_lowlink.put(v.id,	Math.min(v_lowlink.get(v.id), v_index.get(v_prime.id)));
				}
			}
		}
		boolean isAcc = false;
		if(v_lowlink.get(v.id).intValue()==v_index.get(v.id).intValue()){
			int numStates = 0;
			FAState state = null;
			while(! S.empty()){
				FAState t=S.pop();
				++ numStates;
				if(fa.F.contains(t)) {
					f = t;
					isAcc = true;
				}// there exists a final state
				state = t;
				if(t.id==v.id)
					break;
			}
			
			if(numStates == 1){
				if(!( state.getNext()!=null 
				  &&  state.getNext().contains(state)
				    )
				  ){
					return false;
				}
			}
		}
		
		return isAcc;
	}
	
	Pair<List<FAState>, List<FAState>> run = null;
	Pair<List<String>, List<String>> word = null;
	
	public void findpath() {
		if(f == null) return ;
		// get a shortest cycle path
		PathFinder finder = new PathFinder(fa);
		// finite prefix
		finder.setSourceState(fa.getInitialState());
		finder.setTargetState(f);
		finder.findPath();
		Pair<List<FAState>, List<String>> result = finder.getPath();
		List<FAState> prefixRun = result.getLeft();
		List<String> prefixWord = result.getRight();
		
		// cycle path
		finder.setSourceState(f);
		finder.setTargetState(f);
		result = finder.findCycle();
		
		run = new Pair<>(prefixRun, result.getLeft());
		word = new Pair<>(prefixWord, result.getRight());
	}
	
	public Pair<List<FAState>, List<FAState>> getInifinteRun() {
		return run;
	}
	
	public Pair<List<String>, List<String>> getInifinteWord() {
		return word;
	}
	
/*
procedure tarjan(v)
  index = index + 1
  S.push(v)                       // Push v on the stack
  forall (v, v') in E do          // Consider successors of v
    if (v'.index is undefined)    // Was successor v' visited?
        tarjan(v')                // Recurse
        v.lowlink = min(v.lowlink, v'.lowlink)
    else if (v' is in S)          // Was successor v' in stack S? 
        v.lowlink = min(v.lowlink, v'.index)
  if (v.lowlink == v.index)       // Is v the root of an SCC?
    print "SCC:"
    repeat
      v' = S.pop
      print v'
    until (v' == v)

*/
	

}

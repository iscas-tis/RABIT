/* Richard Mayr                                                           */
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

package algorithms;

import java.util.LinkedList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.List;

import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.HashSet;
import datastructure.Pair;
import datastructure.State_Label;


/** This implements the powerset construction for NFA
    and complementation for DFA.
 * 
 * @author Richard Mayr
 * 
 */

public class Determinization{

    private boolean intersect(Set<FAState> x, Set<FAState> y){
	Set<FAState> z = new TreeSet<FAState>();
	z.addAll(x);
	z.removeAll(y);
	return(z.size() < x.size());
    }

    private Set<FAState> get_set(LinkedList<Pair<FAState, Set<FAState>>> macro_Map, FAState state){
	Iterator<Pair<FAState, Set<FAState>>> it = macro_Map.iterator();
	while(it.hasNext()){
	    Pair<FAState, Set<FAState>> p = it.next();
	    if(p.getLeft()==state) return(p.getRight());
	}
	return null;
    }

    private FAState get_state(LinkedList<Pair<FAState, Set<FAState>>> macro_Map, Set<FAState> stateset){
	Iterator<Pair<FAState, Set<FAState>>> it = macro_Map.iterator();
	while(it.hasNext()){
	    Pair<FAState, Set<FAState>> p = it.next();
	    if(p.getRight().equals(stateset)) return(p.getLeft());
	}
	return null;
      }


    /*
      The implements the powerset construction for NFA.
      aut: NFA. Will not be modified.
      alpha: specifies the alphabet of the construction. Must be a superset of the alphabet used in aut.
      limit: An upper limit on the states of the resulting DFA. If exceeded, it returns null.
      Result: A DFA, or null of the state limit is exceeded.
     */

    public FiniteAutomaton PowersetNFA(FiniteAutomaton aut, Set<String> alpha, int limit) {

	int states=0;
FiniteAutomaton result = new FiniteAutomaton();
result.name = aut.name;

LinkedList<Pair<FAState, Set<FAState>>> macro_Map = new LinkedList<Pair<FAState, Set<FAState>>>();
TreeSet<FAState> toProcess = new TreeSet<FAState>();
FAState state;
Set<FAState> stateset;
Set<String> alphabet = aut.getAllTransitionSymbols();
if(!alpha.containsAll(alphabet)) return null;

// create initial macrostate and add it to statemaps
state = result.createState();
states++;
result.setInitialState(state);
toProcess.add(state);
stateset = new TreeSet<FAState>();
stateset.add(aut.getInitialState());
if(aut.F.contains(aut.getInitialState())) result.F.add(state);
macro_Map.addLast(new Pair<FAState,Set<FAState>>(state, stateset));

while(!toProcess.isEmpty()){
    state = toProcess.first();
    toProcess.remove(state);
    stateset = get_set(macro_Map,state);
    Iterator<String> sym_it = alpha.iterator();
    while(sym_it.hasNext()){
	String sym=sym_it.next();
	Set<FAState> stateset2 = new TreeSet<FAState>();
	Iterator<FAState> stateset_it = stateset.iterator();
	while(stateset_it.hasNext()){
	    FAState x = stateset_it.next();
	    if(x.getNext(sym) != null) stateset2.addAll(x.getNext(sym));
	}
	FAState state2 = get_state(macro_Map,stateset2);
	if(state2 != null){
	    result.addTransition(state, state2, sym);
	} else{
	    state2 = result.createState();
	    states++; if(states > limit) return null;
	    result.addTransition(state, state2, sym);
	    toProcess.add(state2);
	    if(intersect(aut.F, stateset2)) result.F.add(state2);
	    macro_Map.addLast(new Pair<FAState,Set<FAState>>(state2, stateset2));
	}
    }
}
return result;
}


    /* Modifies the input aut to become its complement and returns it. */

public FiniteAutomaton ComplementDFA(FiniteAutomaton aut) {

TreeSet<FAState> s = new TreeSet<FAState>();
s.addAll(aut.states);
s.removeAll(aut.F);
aut.F.clear();
aut.F.addAll(s);
return aut;
}



// End of class
}


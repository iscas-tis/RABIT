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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;

public class Membership {

	private FiniteAutomaton automaton;
	
	public Membership(FiniteAutomaton aut) {
		this.automaton = aut;
	}

	public boolean checkMembership(List<String> word) {
		assert  word != null;
		TreeSet<FAState> statesPrev = new TreeSet<FAState>();
		TreeSet<FAState> statesCurr = null;
		statesPrev.add(automaton.getInitialState());
		for(String letter : word) {
			statesCurr = new TreeSet<FAState>();
			for(FAState state : statesPrev) {
				statesCurr.addAll(state.getNext(letter));
			}
			statesPrev = statesCurr;
		}
		
		for(FAState state : statesPrev) {
			if(automaton.F.contains(state)) return true;
		}
		return false;
	}
	

	
	/**
	 * First constuct product and check emptiness 
	 * */
	public boolean checkMembership(List<String> prefix, List<String> suffix) {
		AutomatonBuilder builder = new AutomatonBuilder(prefix, suffix);
		FiniteAutomaton b = builder.build();
		FiniteAutomaton c = ProductBuilder.build(automaton, b);
		EmptinessCheck checker = new EmptinessCheck(c);
		return ! checker.isEmpty();
	}

	

	
	public static void main(String []args) {

		FiniteAutomaton aut = new FiniteAutomaton();
		FAState init = aut.createState();
		aut.setInitialState(init);
		
		FAState a = aut.createState();
		aut.addTransition(init, a, "a");
		FAState b = aut.createState();
		aut.addTransition(init, b, "b");
		FAState ab = aut.createState();
		aut.addTransition(a, ab, "b");
		aut.addTransition(ab, a, "a");
		aut.addTransition(ab, b, "b");
		
		aut.addTransition(b, b, "a");
		aut.addTransition(b, b, "b");
		aut.F.add(ab);
		List<String> prefix = new ArrayList<>();
		List<String> suffix = new ArrayList<>();
		
		prefix.add("a");
		prefix.add("b");
		
		suffix.add("a");
		suffix.add("b");
		
		Membership memebrship = new Membership(aut);
		System.out.println("result : " + memebrship.checkMembership(prefix, suffix));
		suffix.remove("a");
		System.out.println("result : " + memebrship.checkMembership(prefix, suffix));
	}
	


}

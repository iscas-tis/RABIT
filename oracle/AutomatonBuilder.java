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
import java.util.List;

import automata.FAState;
import automata.FiniteAutomaton;


public class AutomatonBuilder {
	
	private List<String> prefix;
	private List<String> suffix;
	
	public AutomatonBuilder(List<String> prefix, List<String> suffix) {
		this.prefix = prefix;
		this.suffix = suffix;
	}
	
	public FiniteAutomaton build() {
		FiniteAutomaton c = new FiniteAutomaton();
		FAState init = c.createState();
		c.setInitialState(init);
		
		FAState curr = init;
		FAState acc = null;
		int j ;
		
		if(prefix.size() == 0) {
			c.F.add(init);
			acc = init;
		}else {
			
			acc = c.createState();
			c.F.add(acc);
			j = prefix.size() - 1;
			
			for(int i = 0; i < j; i ++) {
				FAState s = c.createState();
				c.addTransition(curr, s, prefix.get(i));
				curr = s;
			}
			
			c.addTransition(curr, acc, prefix.get(j));
			
		}
		
		if(suffix.size() == 0) return c;

		curr = acc;
		j = suffix.size() - 1;
		// every state is a accepting state
		for(int i = 0; i < j; i ++) {
			FAState s = c.createState();
			c.addTransition(curr, s, suffix.get(i));
			curr = s;
			c.F.add(s);
		}
		
		c.addTransition(curr, acc, suffix.get(j));

		return c;
	}
	
	public static void main(String[] args) {
		List<String> prefix = new ArrayList<>();
		List<String> suffix = new ArrayList<>();
		prefix.add("a");
		prefix.add("c");
		prefix.add("a");
		//prefix.add("c");
		
		suffix.add("c");
		suffix.add("a");
		suffix.add("a");
		//suffix.add("c");

		//suffix.add("b");
		//suffix.add("a");
		
		AutomatonBuilder autBuilder = new AutomatonBuilder(prefix, suffix);
	    FiniteAutomaton aut = autBuilder.build();
		AutomatonPrinter.print(aut, System.out);

	}

}

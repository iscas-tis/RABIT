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

public class AutomatonWord {
	private final List<String> prefix;
	private final List<String> suffix;
	private final int numStates ;
	// u,v 
	// 0- u[0] -> 1 -u[1]-> 2-> ... - u[n]-> n+1 - v[0]-> n+2... n+k+1 - v[k] -> n+1   
	public AutomatonWord(List<String> prefix, List<String> suffix) {
		this.prefix = prefix;
		this.suffix = suffix;
		if(suffix.size() == 0){
			this.numStates = prefix.size() + 1;
		}
		else {
			this.numStates = prefix.size() + suffix.size();
		}
	}
	
	public int getInitState() {
		return 0;
	}
	
	public int getNumStates() {
		return numStates;
	}
	
	public String getNextLabel(int state) {
		assert state < numStates;
		if(state < prefix.size()) return prefix.get(state);
		if(suffix.size() == 0 ) return "";
		return suffix.get(state - prefix.size());
	}
	
	public int getNextState(int state) {
		if(state < numStates - 1) {
			return state + 1;
		}
		return prefix.size();
	}
	
	public boolean isAccepted(int state) {
		assert state < numStates;
		return state >= prefix.size();
	}
	
	public String toString() {
		StringBuilder builder = new StringBuilder();
		for(int i = 0; i < getNumStates(); i ++) {
			builder.append( i + " -" + getNextLabel(i) + "-> " + getNextState(i) + "\n");
		}
		builder.append("init: " + getInitState() + "\n");
		//F
		builder.append("final: ");
		for(int i = 0; i < getNumStates(); i ++) {
			if(isAccepted(i)) builder.append(" " + i);
		}
		builder.append("\n");
		return builder.toString();
	}
	
	public static void main(String[] args) {
		List<String> prefix = new ArrayList<>();
		List<String> suffix = new ArrayList<>();
		prefix.add("a");
		suffix.add("b");
		suffix.add("a");
		
		AutomatonWord aut = new AutomatonWord(prefix, suffix);
		System.out.println(aut);
		
		prefix.clear();
		aut = new AutomatonWord(prefix, suffix);
		System.out.println(aut);
		suffix.remove("a");
		aut = new AutomatonWord(prefix, suffix);
		System.out.println(aut);
		suffix.remove("b");
		prefix.add("a");
		aut = new AutomatonWord(prefix, suffix);
		System.out.println(aut);
	}
}

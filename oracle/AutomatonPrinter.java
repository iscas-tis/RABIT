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

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Set;

import automata.FAState;
import automata.FiniteAutomaton;

public class AutomatonPrinter {
	public static void print(FiniteAutomaton aut, OutputStream stream) {
		
		PrintStream out = new PrintStream(stream);
        out.println("//Buechi ");
        out.println("digraph {");
        
        Set<FAState> states = aut.states;
        for (FAState state : states) {
            out.print("  " + state.id + " [label=\"" +  state.id + "\"");
            if(aut.F.contains(state)) out.print(", shape = doublecircle");
            else out.print(", shape = circle");
            out.println("];");
            for (String label : aut.getAllTransitionSymbols()) {
            	Set<FAState> succs = state.getNext(label);
            	if(succs == null) continue;
            	for(FAState succ : succs) {
            		out.println("  " + state.id + " -> " + succ.id + " [label=\"" + label + "\"];");
            	}
            }
        }	
        out.println("  " + states.size() + " [label=\"\", shape = plaintext];");
        FAState initState = aut.getInitialState();
        out.println("  " + states.size() + " -> " + initState.id + " [label=\"\"];");
        out.println();
        out.println("}");
   }
}

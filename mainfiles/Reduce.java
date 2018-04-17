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

/*
import java.util.Random;
import java.util.TreeMap;
import java.util.Iterator;

import java.util.Arrays;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
*/

import automata.FAState;
import automata.FiniteAutomaton;
import algorithms.Minimization;
import algorithms.ParallelMinimization;

/**
 * 
 * @author Richard Mayr, Yu-Fang Chen
 * 
 */
public class Reduce {
    // static long timeout=0;
    // static boolean timeout_set=false;

    public static void main(String[] args) {
	boolean light=false;
	boolean nojump=false;
	boolean pebble=false;
	boolean finite=false;
	boolean parallel=false;
	boolean sat=false;
	boolean sat2=false;
	boolean outputname=false;
	String newname="";

		System.out.println("Reduce (v. 2.4.4): A tool for reducing Buchi automata and finite automata.");
		for(int i=0;i<args.length;i++){
			if(args[i].compareTo("-h")==0){
				System.out.println("Usage: java -jar Reduce.jar aut.ba  n [-light|-nojump|-pebble|-sat|-sat2] [-finite] [-par]");
				System.out.println("-h: Show this page");
				System.out.println("aut.ba is a Buchi automaton (or finite automaton, resp.)");
				System.out.println("n >= 1 is a natural number to set the lookahead of the minimization. On average, larger n takes longer to compute and yields smaller automata. We recommend to use 12.");
				System.out.println("Options light/nojump/pebble/sat/sat2 are mutually exclusive, but each can be combined with options -finite and -par.");
				System.out.println("No option: The default. Best balance between minimization and computation time, on average.");
				System.out.println("-light: Only remove dead states and quotient with lookahead delayed simulation. For comparison only.");
				System.out.println("-nojump: Like the default, except that it does not use jumping simulation.");
				System.out.println("-pebble: Default, plus use of 2 pebbles in some cases. Very slow. On average it is better to use the default with higher lookahead instead.");
				System.out.println("-sat: Default, plus transition saturation (allow adding transitions). Slower. May yield fewer states but possibly more transitions.");
				System.out.println("-sat2: More aggressive version of -sat. Slower.");
				System.out.println("-finite: Reduce finite automata, not Buchi automata.");
				System.out.println("-par: Use fork-join parallelism to speed up the computation.");
				System.out.println("-o name: Save the result in file <name>. (Otherwise, a name is chosen by prepending the used method description to the input name).");
				System.out.println("Output: Reduced automaton.");
				System.exit(0);
			}
			if(args[i].compareTo("-light")==0){
			    light=true;
			}
			else if(args[i].compareTo("-nojump")==0){
			    nojump=true;
			}
			else if(args[i].compareTo("-pebble")==0){
			    pebble=true;
			}
			else if(args[i].compareTo("-sat")==0){
			    sat=true;
			}
			else if(args[i].compareTo("-sat2")==0){
			    sat2=true;
			}
			else if(args[i].compareTo("-finite")==0){
			    finite=true;
			}
			else if(args[i].compareTo("-par")==0){
			    parallel=true;
			}
			else if(args[i].compareTo("-o")==0){
			    outputname=true;
			    newname=args[i+1];
			}
		}

		if(args.length == 0){
		    System.out.println("Invoke with option -h for help.");
				System.exit(0);
		}

                long ttime1, ttime2;
		FiniteAutomaton aut = new FiniteAutomaton(args[0]);
		aut.name=args[0];
		FiniteAutomaton aut2;
		int la = Integer.parseInt(args[1]);

		System.out.println("Input automaton: # of Trans. "+aut.trans+", # of States "+aut.states.size()+".");
		// System.out.println("Number of acc states: "+aut.F.size());
		ttime1=System.currentTimeMillis();

		if(!parallel){
		Minimization x = new Minimization();
		
		if(!finite){
		    // Minimize Buchi aut.
		    if(light) aut2 = x.LightweightMinimize_Buchi(aut, la);
		    else if(nojump) aut2 = x.experimental_noj_Minimize_Buchi(aut, la);
		    else if(pebble) aut2 = x.addpebble_Minimize_Buchi(aut, la);
		    else if(sat) aut2 = x.saturate_Minimize_Buchi(aut, la);
		    else if(sat2) aut2 = x.sat2_Minimize_Buchi(aut, la);
		    else aut2 = x.Minimize_Buchi(aut, la);
		}
		else{
		    // Minimize finite aut.
		    if(light) aut2 = x.LightweightMinimize_Finite(aut, la);
		    else if(nojump) aut2 = x.Minimize_Finite(aut, la, true, false, false);
		    else if(pebble) aut2 = x.Minimize_Finite(aut, la, true, true, true);
		    else if(sat) aut2 = x.saturate_Minimize_Finite(aut, la);
		    else if(sat2) aut2 = x.sat2_Minimize_Finite(aut, la);
		    else aut2 = x.Minimize_Finite(aut, la, true, true, false);
		}
		ttime2=System.currentTimeMillis();    
		}
		else{
		ParallelMinimization x = new ParallelMinimization();
		
		if(!finite){
		    // Minimize Buchi aut.
		    if(light) aut2 = x.LightweightMinimize_Buchi(aut, la);
		    else if(nojump) aut2 = x.experimental_noj_Minimize_Buchi(aut, la);
		    else if(pebble) aut2 = x.addpebble_Minimize_Buchi(aut, la);
		    else if(sat) aut2 = x.saturate_Minimize_Buchi(aut, la);
		    else if(sat2) aut2 = x.sat2_Minimize_Buchi(aut, la);
		    else aut2 = x.Minimize_Buchi(aut, la);
		}
		else{
		    // Minimize finite aut.
		    if(light) aut2 = x.LightweightMinimize_Finite(aut, la);
		    else if(nojump) aut2 = x.Minimize_Finite(aut, la, true, false, false);
		    else if(pebble) aut2 = x.Minimize_Finite(aut, la, true, true, true);
		    else if(sat) aut2 = x.saturate_Minimize_Finite(aut, la);
		    else if(sat2) aut2 = x.sat2_Minimize_Finite(aut, la);
		    else aut2 = x.Minimize_Finite(aut, la, true, true, false);
		}
		ttime2=System.currentTimeMillis();
		}
		
		if(!outputname){
		    if(light) newname="light_reduced_"+la+"_"+aut.name;
		    else if(nojump) newname="nojump_reduced_"+la+"_"+aut.name;
		    else if(pebble) newname="pebble_reduced_"+la+"_"+aut.name;
		    else if(sat) newname="sat_reduced_"+la+"_"+aut.name;
		    else if(sat2) newname="sat2_reduced_"+la+"_"+aut.name;
		    else newname="reduced_"+la+"_"+aut.name;
		    if(finite) newname="finite_"+newname;
		}

		aut2.saveAutomaton(newname);

		System.out.println("Reduced automaton: # of Trans. "+aut2.trans+", # of States "+aut2.states.size()+".");
		System.out.println("Saved as "+newname);
		System.out.println("Time for the reduction (ms): "+(ttime2-ttime1)+".");
		return;
    }
}

/* Written by Yu-Fang Chen, Richard Mayr, and Chih-Duo Hong               */
/* Copyright (c) 2010                  	                                  */
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

import java.util.Random;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;

/**
 * 
 * @author Yu-Fang Chen
 * 
 */
public class TV {
	public static void main(String[] args) {	
		Random r = new Random();
		if(args.length<4){
		    System.out.println("A generator of Tabakov-Vardi random automata.");
			System.out.println("Usage: java -jar TV.jar size td ad filename");
			System.out.println("Size: number of states.");
			System.out.println("td=transition density, typically between 1.1 and 4.5");
			System.out.println("ad=acceptance density, must be between 0 and 1.0, e.g., 0.5");
			System.out.println("filename=The filename (without extension) where the automaton is stored.");
			System.out.println("Output: filename.ba");
			System.out.println("Example: java -jar TV.jar 100 1.9 0.8 test");
		}else{
			int size=Integer.parseInt(args[0]);
			float td=Float.parseFloat(args[1]);
			float fd=Float.parseFloat(args[2]);
			String name=args[3];
			FiniteAutomaton ba=genRandomTV(size, td, fd,2);
			    //System.out.println(ba);
			ba.saveAutomaton(name+".ba");
		}
	}

	
	
	/**
	 *  Generate automata using Tabakov and Vardi's approach
	 * 
	 *  @param num
	 *  
	 *  @return a random finite automaton
	 *  @author Yu-Fang Chen
	 */
	public static FiniteAutomaton genRandomTV(int size, float td, float fd, int alphabetSize){
		FiniteAutomaton result = new FiniteAutomaton();
		TreeMap<Integer,FAState> st=new TreeMap<Integer,FAState>();

		
		Random r = new Random();
		TreeSet<Integer> added=new TreeSet<Integer>(); 
		
		for(int i=0;i<size;i++){
			st.put(i, result.createState());
		}

		for(int n=0;n<Math.round(size*fd)-1;n++){
			int i=r.nextInt(size-1);
			if(!added.contains(i+1)){
				result.F.add(st.get(i+1));
				added.add(i+1);
			}else
				n--;
		}
		
		result.setInitialState(st.get(0));
		result.F.add(st.get(0));
		
		int transNum=Math.round(td*size);

		
		for(int k=0;k<alphabetSize;k++){
		        added.clear(); 
			for(int n=0;n<transNum;n++){
					int i=r.nextInt(size);
					int j=r.nextInt(size);
					if(!added.contains(i*size+j)){
						result.addTransition(st.get(i),st.get(j),("a"+k));
						added.add(i*size+j);
					}
					else
						n--;
			}
		}
		return result;
	}
}


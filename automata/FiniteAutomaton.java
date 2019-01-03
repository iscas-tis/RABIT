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

package automata;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.io.*;

public class FiniteAutomaton{
	public TreeSet<FAState> states;
	public TreeSet<FAState> F;
	public TreeSet<String> alphabet;
	public int trans=0;
	FAState init;
	private int num=0;
	public String name="";
	public FiniteAutomaton(){
		init();
	}

	public FiniteAutomaton(File source) throws IOException{
		loadAutomaton(source);
	}
	public FiniteAutomaton(String filename){
		if(!loadAutomaton(filename))
			throw new InvalidAutomatonFormat("The source file \""+filename+"\" does not define a valid automaton.");
	}
	public void init()
	{
		states=new TreeSet<FAState>();
		F=new TreeSet<FAState>();
		alphabet=new TreeSet<String>();
	}
	public FAState createState() {
		FAState st=new FAState(num, this);
		num++;
		states.add(st);
		return st;
	}

	public FAState getInitialState() {
		return init;
	}

	public void setInitialState(FAState state) {
		init=state;
	}
	
	public Set<String> getAllTransitionSymbols() {
		return alphabet;
	}
	public Set<String> getAllTransitionSymbolsAL() {
		return alphabet;
	}
	public void addTransition(FAState state, FAState state2, String label) {
		if(state.getNext(label)!=null)
			if(state.getNext(label).contains(state2))
				return;
		trans++;
		if(!alphabet.contains(label)) 
		{
			alphabet.add(label);
		}
		state.addNext(label,state2,this);
		state2.addPre(label, state);
	}
	@Override
	public String toString() {
		String result="\n";
		Iterator<FAState> st_it=states.iterator();
		while(st_it.hasNext()){
			FAState st=st_it.next();
			Iterator<String> label_it=st.nextIt();
			while(label_it.hasNext()){
				String label=label_it.next();
				Iterator<FAState> to_it=st.getNext(label).iterator();
				while(to_it.hasNext()){
					FAState to=to_it.next();
					result+=(st+" --"+label+"-->"+to+"\n");
				}
			}
		}
		result+="\nInit:"+init;
		result+="\nACC:"+F+"\n";
		return result;
	}

	public void removeState(FAState state){
	    // First remove all incoming transitions
	    Iterator<String> sym_it = state.preIt();
	    while(sym_it.hasNext()){
				String sym=sym_it.next();
				Iterator<FAState> prestate_it = state.getPre(sym).iterator();
				while(prestate_it.hasNext()){
				    FAState prestate=prestate_it.next();
				    prestate.getNext(sym).remove(state);
				    trans--;
				}
	    }
	    // Now remove all outgoing transitions
	    sym_it = state.nextIt();
	    while(sym_it.hasNext()){
				String sym=sym_it.next();
				Iterator<FAState> nextstate_it = state.getNext(sym).iterator();
				while(nextstate_it.hasNext()){
				    FAState nextstate=nextstate_it.next();
				    nextstate.getPre(sym).remove(state);
				    trans--;
				}
	    }
	    // Now remove the state `state' itself
	    states.remove(state);
	    if(F.contains(state)) F.remove(state);
	    num--;
	}

	public String toMh() {
		String result=states.size()+" ";
		HashMap<Integer,Integer> stMap=new HashMap<Integer,Integer>();
		HashMap<String,Integer> labelMap=new HashMap<String,Integer>();
		int currentMaxLabel=0;
		Iterator<FAState> st_it=states.iterator();
		int swap=1;
		while(st_it.hasNext()){
			FAState st=st_it.next();
			if(st.getID()==init.id){
				stMap.put(st.getID(), 1);
				swap=st.getID();
			}else{
				stMap.put(st.getID(),st.getID()+1);
			}
		}			
		stMap.put(0,swap+1);
		
		st_it=states.iterator();
		while(st_it.hasNext()){
			FAState st=st_it.next();
			if(F.contains(st))
				result=result+stMap.get(st.id)+" ";
		}
		result=result+"- ";
		
		
		st_it=states.iterator();
		while(st_it.hasNext()){
			FAState st=st_it.next();
			Iterator<String> label_it=st.nextIt();
			while(label_it.hasNext()){
				String label=label_it.next();
				if(!labelMap.containsKey(label)){
					labelMap.put(label, currentMaxLabel);
					currentMaxLabel++;
				}
				Iterator<FAState> to_it=st.getNext(label).iterator();
				while(to_it.hasNext()){
					FAState to=to_it.next();
					result+=(stMap.get(st.getID())+" ");
					result+=(labelMap.get(label)+" ");
					result+=(stMap.get(to.getID())+" ");
				}
			}
		}
		result+=" ";
		return result;
	}
	
	public String toString2() {
		String result="\n";
		Iterator<FAState> st_it=states.iterator();
		while(st_it.hasNext()){
			FAState st=st_it.next();
			Iterator<String> label_it=st.nextIt();
			while(label_it.hasNext()){
				String label=label_it.next();
				Iterator<FAState> to_it=st.getNext(label).iterator();
				while(to_it.hasNext()){
					FAState to=to_it.next();
					result+=("t("+st.id+","+to.id+",\""+label+"\");");

				}
			}
			result+="\n";
		}
		result+="\nInit:"+init+"\n";
		st_it=F.iterator();
		while(st_it.hasNext()){
			result+="f("+st_it.next().id+");\n";
		}
		return result;
	}	
	public boolean loadAutomaton(String filename)
	{
		try{
			return loadAutomaton(new File(filename));
		}catch(IOException e){
			System.out.println(e.getMessage());
			return false;
		}		
	}	
	public boolean loadAutomaton(File source) throws IOException 
	{
		Map<String, FAState> stMap=new TreeMap<String, FAState>(); 
		BufferedReader input = null;	
			input = new BufferedReader(new FileReader(source));
			boolean init=true, trans=true;
			init();
			while(input.ready()){
				String s = input.readLine();
				// Lines starting with % are comments and ignored.
				if(s.isEmpty()) continue;
				if(s.charAt(0)=='%') continue;
				if(init)
				{
					if(s.indexOf(',')<0)
					{
						FAState newState=stMap.get(s);
						if(newState==null){
							newState=createState();
							stMap.put(s, newState);
						}
						setInitialState(newState);
						init=false;
						continue;
					}
				}
				if(trans)
				{
					String[] ss = s.split("[,\\->]");
					if(ss.length==4)
					{
						FAState fromState=stMap.get(ss[1]);
						if(fromState==null){
							fromState=createState();
							stMap.put(ss[1], fromState);
						}
						FAState toState=stMap.get(ss[3]);
						if(toState==null){
							toState=createState();
							stMap.put(ss[3], toState);
						}
						if(init)
							setInitialState(fromState);
						addTransition(fromState,toState,ss[0]);
						init=false;
						continue;
					}
					trans = false;
				}				
				if(s.indexOf(',')<0){
					FAState newState=stMap.get(s);
					if(newState==null){
						newState=createState();
						stMap.put(s, newState);
					}
					F.add(newState);
					if(init)
						setInitialState(newState);
				}
				init=false;
			};
			if(trans)				
				F.addAll(states);
			input.close();
			return (this.init!=null)&&(this.num>0);
	}	
	public boolean saveAutomaton(String filename)
	{
		try{	
			return saveAutomaton(new File(filename));
		}catch(IOException e){
			System.out.println(e.getMessage());
			return false;
		}		
	}
	private boolean saveEmptyAutomaton(BufferedWriter output) throws IOException {
	    output.write("[0]\n");
	    for(String label : alphabet) {
	        output.write(label + ",[1]->[1]\n");
	    }
	    output.write("[1]\n");
	    return true;
	}
	
	public boolean saveAutomaton(File dest) throws IOException
	{
			BufferedWriter output;		
			FAState[] states = this.states.toArray(new FAState[0]);	
			output = new BufferedWriter(new FileWriter(dest));
			
			if(F.isEmpty()) {
			    saveEmptyAutomaton(output);
		         output.flush();
		         output.close();
			    return true;
			}
			
			output.write("["+getInitialState().id+"]\n");
			
			for(int i=0;i<states.length;i++)
			{
				Iterator<String> label_it = states[i].nextIt();
				String from_name = "["+states[i].id+"]";
				
				while(label_it.hasNext()){
					String label = label_it.next();
					String prefix = label + "," + from_name + "->";
					Set<FAState> next_set = states[i].getNext(label);
					Iterator<FAState> next_it = next_set.iterator();
					while(next_it.hasNext())
					{
						FAState s = next_it.next();
						String to_name = "["+s.id+"]";						
						output.write(prefix+to_name+"\n");						
					}
				}
			}
			Iterator<FAState> st_it=F.iterator();
			while(st_it.hasNext()){
				FAState st=st_it.next();
				output.write("["+st.id+"]\n");				
			}
			output.flush();
			output.close();
			return true;		
	}



	public boolean saveAutomatonTimbuk(String filename)
	{
		try{	
		    return saveAutomatonTimbuk(new File(filename), filename);
		}catch(IOException e){
			System.out.println(e.getMessage());
			return false;
		}		
	}
	    public boolean saveAutomatonTimbuk(File dest, String filename) throws IOException
	{
			BufferedWriter output;		
			FAState[] states = this.states.toArray(new FAState[0]);	
			output = new BufferedWriter(new FileWriter(dest));
			
			output.write("Ops");
			// dummy start transition
			output.write(" start:0");
			Iterator<String> alph_it = alphabet.iterator();
			while(alph_it.hasNext()){
			    String alph = alph_it.next();
			    output.write(" "+"a"+alph+":1");
			}
			output.write("\n");
			String[] words = filename.split ("\\.");
			output.write("Automaton "+words[0]+"\n");
			output.write("States");
			for(int i=0;i<states.length;i++){
			    output.write(" q"+states[i].id);
			}
			output.write("\n");
			output.write("Final States");
			Iterator<FAState> st_it=F.iterator();
			while(st_it.hasNext()){
				FAState st=st_it.next();
				output.write(" q"+st.id);	
			}
			output.write("\n");
			output.write("Transitions\n");
			// Start transition
			output.write("start() -> "+"q"+getInitialState().id+"\n");
			
			for(int i=0;i<states.length;i++){
				Iterator<String> label_it = states[i].nextIt();
				String from_name = "q"+states[i].id;
				while(label_it.hasNext()){
					String label = label_it.next();
					Set<FAState> next_set = states[i].getNext(label);
					Iterator<FAState> next_it = next_set.iterator();
					while(next_it.hasNext()){
						FAState s = next_it.next();
						String to_name = "q"+s.id;						
						output.write("a"+label+"("+from_name+") -> "+to_name+"\n");					
					}
				}
			}
			output.flush();
			output.close();
			return true;		
	}




	public boolean saveAutomatonTimbuk2(String filename)
	{
		try{	
		    return saveAutomatonTimbuk2(new File(filename), filename);
		}catch(IOException e){
			System.out.println(e.getMessage());
			return false;
		}		
	}
	    public boolean saveAutomatonTimbuk2(File dest, String filename) throws IOException
	{
			BufferedWriter output;		
			FAState[] states = this.states.toArray(new FAState[0]);	
			output = new BufferedWriter(new FileWriter(dest));
			
			output.write("Ops");
			// dummy accept symbol for leaf rule
			output.write(" accept:0");
			Iterator<String> alph_it = alphabet.iterator();
			while(alph_it.hasNext()){
			    String alph = alph_it.next();
			    output.write(" "+"a"+alph+":1");
			}
			output.write("\n");
			String[] words = filename.split ("\\.");
			output.write("Automaton "+words[0]+"\n");
			output.write("States");
			for(int i=0;i<states.length;i++){
			    output.write(" q"+states[i].id);
			}
			output.write("\n");
			// On one final, i.e., our one inital state
			output.write("Final States "+"q"+getInitialState().id+"\n");
			
			output.write("Transitions\n");
						
			for(int i=0;i<states.length;i++){
				Iterator<String> label_it = states[i].nextIt();
				String from_name = "q"+states[i].id;
				while(label_it.hasNext()){
					String label = label_it.next();
					Set<FAState> next_set = states[i].getNext(label);
					Iterator<FAState> next_it = next_set.iterator();
					while(next_it.hasNext()){
						FAState s = next_it.next();
						String to_name = "q"+s.id;
						// reverse to/from for Timbuk format
						output.write("a"+label+"("+to_name+") -> "+from_name+"\n");					
					}
				}
			}

			// Now add leaf rules
			Iterator<FAState> st_it=F.iterator();
			while(st_it.hasNext()){
				FAState st=st_it.next();
				output.write("accept() -> "+"q"+st.id+"\n");
			}
			output.write("\n");

			output.flush();
			output.close();
			return true;		
	}




//	public static void main(String args[])
//	{
//		String file = "mcs.2.1.crtcl2.final.ba";
//		System.out.println(file+" started...");
//		FiniteAutomaton fa = new FiniteAutomaton();
//		fa.loadAutomaton(file);
//		fa.saveAutomaton("mcs.2.1.crtcl2.final.ba_");
//		System.out.println("done!");
//	}
}

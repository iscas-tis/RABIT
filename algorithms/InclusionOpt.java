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

package algorithms;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;
import comparator.StatePairComparator;
import comparator.SuperGraphComparator;
import datastructure.Arc;
import datastructure.OneToOneTreeMap;
import datastructure.Pair;



/**
 * 
 * @author Yu-Fang Chen
 * 
 */
public class InclusionOpt extends Thread{
	boolean opt2=true;
	public boolean debug=false;
	boolean quotient=true;
	public int removedCnt;
	public boolean included=true;
	private TreeMap<String,TreeSet<Integer>> Tail=new TreeMap<String,TreeSet<Integer>>();
	private TreeMap<String,TreeSet<Integer>> Head=new TreeMap<String,TreeSet<Integer>>();
	private long runTime;
	private boolean stop=false;
	private Set<Pair<FAState,FAState>> rel_spec, rel_system;
	FiniteAutomaton spec, system;
	String showSim(Set<Pair<FAState,FAState>> sim){
		String result="";
		Iterator<Pair<FAState,FAState>> sim_it=sim.iterator();
		while(sim_it.hasNext()){
			Pair<FAState,FAState> p=sim_it.next();
			if(p.getLeft().getID()!=p.getRight().getID()){
				result+=("("+p.getLeft()+","+p.getRight()+")");
			}
			
		}
		return result;
	}
	void debug(String out){
		if(debug)
		System.out.println(out);
	}
	public InclusionOpt(FiniteAutomaton system, FiniteAutomaton spec){
		this.spec=spec;
		this.system=system;
	}
	/**
	 * Simplify a finite automaton by merging simulation equivalent states
	 * @param fa: a finite automaton
	 * @param Sim: some simulation rel_specation over states in the spec automaton
	 * 
	 * @return an equivalent finite automaton
	 */
	private FiniteAutomaton quotient(FiniteAutomaton fa, Set<Pair<FAState,FAState>> rel) {
		FiniteAutomaton result=new FiniteAutomaton();
		result.name=fa.name;
		TreeMap<FAState,FAState> map=new TreeMap<FAState,FAState>();
		TreeMap<FAState,FAState> reducedMap=new TreeMap<FAState,FAState>();
		
		Iterator<FAState> state_it=fa.states.iterator();
		while(state_it.hasNext()){
			FAState state=state_it.next();
			map.put(state, state);
			Iterator<FAState> state_it2=fa.states.iterator();
			while(state_it2.hasNext()){
				FAState state2=state_it2.next();
				if(rel.contains(new Pair<FAState,FAState>(state,state2)) &&
					rel.contains(new Pair<FAState,FAState>(state2,state))){
					map.put(state,state2);
				}
			}			
		}

		FAState init=result.createState();
		reducedMap.put(map.get(fa.getInitialState()), init);
		result.setInitialState(init);

		state_it=fa.states.iterator();
		while(state_it.hasNext()){
			FAState state=state_it.next();
			if(!reducedMap.containsKey(map.get(state))){
				reducedMap.put(map.get(state), result.createState());
			}
			if(fa.F.contains(state)){
				result.F.add(reducedMap.get(map.get(state)));
			}
			Iterator<String> sym_it=state.nextIt();
			while(sym_it.hasNext()){
				String sym=sym_it.next();
				Iterator<FAState> to_it=state.getNext(sym).iterator();
				while(to_it.hasNext()){
					FAState to=to_it.next();
					if(!reducedMap.containsKey(map.get(to))){
						reducedMap.put(map.get(to), result.createState());
					}
					result.addTransition(reducedMap.get(map.get(state)), reducedMap.get(map.get(to)), sym);
				}
			}
		}
		Set<Pair<FAState,FAState>> newrel_spec=new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		Iterator<Pair<FAState,FAState>> sim_it=rel.iterator();
		while(sim_it.hasNext()){
			Pair<FAState,FAState> sim=sim_it.next();
			newrel_spec.add(new Pair<FAState,FAState>(reducedMap.get(map.get(sim.getLeft())),reducedMap.get(map.get(sim.getRight()))));
		}
		rel.clear();
		rel.addAll(newrel_spec);
		
		return result;
	}	
	private boolean double_graph_test(Pair<Arc,TreeSet<Arc>> g, Pair<Arc,TreeSet<Arc>> h, int init){
		Arc g_arc=g.getLeft();
		Arc h_arc=h.getLeft();
		
		if(!(rel_system.contains(new Pair<FAState,FAState>(new FAState(h_arc.getFrom(),system),new FAState(h_arc.getTo(),system))) &&
			 rel_system.contains(new Pair<FAState,FAState>(new FAState(h_arc.getFrom(),system),new FAState(g_arc.getTo(),system))) &&
			 system.getInitialState().id==g_arc.getFrom() && system.F.contains(new FAState(h_arc.getFrom(),system))
		)){
			return true;
		}else{
			boolean result = lasso_finding_test(g.getRight(),h.getRight(),init);
			if(!result){
				debug("g_arc: "+g_arc);
				debug("h_arc: "+h_arc);
				debug("init: "+system.getInitialState());
				debug("final: "+system.F);
			}
			return result;
		}
	}	
		
		
	
	private boolean lasso_finding_test(TreeSet<Arc> g, TreeSet<Arc> h, int init){
		if(!Head.containsKey(g.toString())){
			TreeSet<Integer> H=new TreeSet<Integer>();
			Iterator<Arc> arc_g_it=g.iterator();
			while(arc_g_it.hasNext()){
				Arc arc_g=arc_g_it.next();
				if(arc_g.getFrom()==init){
					H.add(arc_g.getTo());
				}
			}
			Head.put(g.toString(), H);
		}
		if(!Tail.containsKey(h.toString())){
			FiniteAutomaton fa=new FiniteAutomaton();
			OneToOneTreeMap<Integer,automata.FAState> st=new OneToOneTreeMap<Integer,automata.FAState>();
			Iterator<Arc> arc_h_it=h.iterator();
			while(arc_h_it.hasNext()){
				Arc arc_h=arc_h_it.next();
				if(!st.containsKey(arc_h.getFrom()))
					st.put(arc_h.getFrom(), fa.createState());
				if(!st.containsKey(arc_h.getTo()))
					st.put(arc_h.getTo(), fa.createState());
				fa.addTransition(st.getValue(arc_h.getFrom()), st.getValue(arc_h.getTo()), arc_h.getLabel()?"1":"0");
			}
			SCC s=new SCC(fa);
			TreeSet<Integer> T=new TreeSet<Integer>();
			Iterator<FAState> s_it=s.getResult().iterator();
			while(s_it.hasNext()){
				T.add(st.getKey(s_it.next()));
			}
			int TailSize=0;
			TreeSet<Arc> isolatedArcs=h;
			while(TailSize!=T.size()){
				TailSize=T.size();
				TreeSet<Arc> isolatedArcsTemp=new TreeSet<Arc>();
				Iterator<Arc> arc_it=isolatedArcs.iterator();
				while(arc_it.hasNext()){
					Arc arc=arc_it.next();
					if(!T.contains(arc.getTo())){
						isolatedArcsTemp.add(arc);
					}else{
						T.add(arc.getFrom());
					}
				}
				isolatedArcs=isolatedArcsTemp;
			}
			Tail.put(h.toString(), T);
		}
		TreeSet<Integer> intersection = new TreeSet<Integer>();
		intersection.addAll(Head.get(g.toString()));
		intersection.retainAll(Tail.get(h.toString()));
		
		if(debug){
			if(intersection.isEmpty()){
				debug("g_graph:"+g+", Head: "+Head.get(g.toString()));
				debug("h_graph:"+h+", Tail: "+Tail.get(h.toString()));
			}
		}
		
		return !intersection.isEmpty();
	}
	
	private Pair<Arc, TreeSet<Arc>> min(Pair<Arc, TreeSet<Arc>> supergraph){
		TreeSet<Arc> result=new TreeSet<Arc>();
		Iterator<Arc> arc_it1 =supergraph.getRight().iterator();
		while(arc_it1.hasNext()){
			Arc cur=arc_it1.next();
			boolean canAdd=true;
			Iterator<Arc> arc_it2 =supergraph.getRight().iterator();
			while(arc_it2.hasNext()){
				Arc other=arc_it2.next();
				if(cur.getFrom()==other.getFrom()){
					if(!cur.getLabel()||other.getLabel()){
						if(cur.getTo()!=other.getTo()){
							if(rel_spec.contains(new Pair<FAState,FAState>(new FAState(cur.getTo(),spec),new FAState(other.getTo(), spec )))){
								if(!rel_spec.contains(new Pair<FAState,FAState>(new FAState(other.getTo(),spec),new FAState(cur.getTo(), spec )))){
									canAdd=false;
									break;
								}else if(cur.getTo()<other.getTo()){
									canAdd=false;
									break;
								}
							}
						}
					}
				}
			}			
			if(canAdd){
				result.add(cur);
			}
		}
		return new Pair<Arc, TreeSet<Arc>>(supergraph.getLeft(),result);
	}
	
	private ArrayList<Pair<Arc, TreeSet<Arc>>> buildSingleCharacterSuperGraphs(){
		ArrayList<Pair<Arc, TreeSet<Arc>>> supergraphs=new ArrayList<Pair<Arc, TreeSet<Arc>>>();
		
		Iterator<String> symbol_it=system.getAllTransitionSymbols().iterator();
		while(symbol_it.hasNext()){
			TreeSet<Arc> graph=new TreeSet<Arc>();
			
			String sym=symbol_it.next();
			Iterator<FAState> from_it=spec.states.iterator();
			while(from_it.hasNext()){
				FAState from=from_it.next();
				if(from.getNext(sym)!=null){
					Iterator<FAState> to_it=from.getNext(sym).iterator();
					while(to_it.hasNext()){
						FAState to=to_it.next();
						if(spec.F.contains(from)||spec.F.contains(to)){
							graph.add(new Arc(from.id,true,to.id));
						}else{
							graph.add(new Arc(from.id,false,to.id));
						}
					}
				}
			}

			from_it=system.states.iterator();
			while(from_it.hasNext()){
				FAState from=from_it.next();
				if(from.getNext(sym)!=null){
					Iterator<FAState> to_it=from.getNext(sym).iterator();
					while(to_it.hasNext()){
						FAState to=to_it.next();
						Arc left_arc=new Arc(from.id,false,to.id);
						Pair<Arc, TreeSet<Arc>> supergraph=new Pair<Arc, TreeSet<Arc>>(left_arc,graph);
						ArrayList<Pair<Arc, TreeSet<Arc>>> toRemove=new ArrayList<Pair<Arc, TreeSet<Arc>>>();
						boolean canAdd=true;
						Iterator<Pair<Arc, TreeSet<Arc>>> old_it=supergraphs.iterator();
						while(old_it.hasNext()){
							Pair<Arc, TreeSet<Arc>> old=old_it.next();
							if(smallerThan(old, supergraph)){
								canAdd=false;
								break;
							}else if(smallerThan(supergraph, old)){
								toRemove.add(old);
							}
						}
						if(canAdd){
							if(opt2)
								supergraphs.add(min(supergraph));
							else
								supergraphs.add(supergraph);
							supergraphs.removeAll(toRemove);
						}
					}
				}
			}
		}
		return supergraphs;
	}

	private Pair<Arc, TreeSet<Arc>> compose(Pair<Arc, TreeSet<Arc>> g, Pair<Arc, TreeSet<Arc>> h){
		TreeSet<Arc> f=new TreeSet<Arc>();
		Iterator<Arc> arc_g_it=g.getRight().iterator();
		while(arc_g_it.hasNext()){
			Arc arc_g=arc_g_it.next();
			Iterator<Arc> arc_h_it=h.getRight().iterator();
			while(arc_h_it.hasNext()){
				Arc arc_h=arc_h_it.next();
				if(arc_g.getTo()==arc_h.getFrom()){
					if(arc_g.getLabel()||arc_h.getLabel()){
						f.add(new Arc(arc_g.getFrom(),true,arc_h.getTo()));
						f.remove(new Arc(arc_g.getFrom(),false,arc_h.getTo()));
					}else{
						if(!f.contains(new Arc(arc_g.getFrom(),true,arc_h.getTo()))){
							f.add(new Arc(arc_g.getFrom(),false,arc_h.getTo()));
						}
					}
				}				
			}			
		}
		return new Pair<Arc, TreeSet<Arc>>(new Arc(g.getLeft().getFrom(),false,h.getLeft().getTo()),f);
	}
	
	boolean smallerThan(Pair<Arc, TreeSet<Arc>> old, Pair<Arc, TreeSet<Arc>> old2){
		Arc old_arc=old.getLeft();
		Arc old2_arc=old2.getLeft();
		if(!(old_arc.getFrom()==old2_arc.getFrom() && 
		rel_system.contains(new Pair<FAState,FAState>(new FAState(old2_arc.getTo(),system),new FAState(old_arc.getTo(),system))))){
			return false;
		}
		
		Iterator<Arc> arc_g_it=old.getRight().iterator();
		while(arc_g_it.hasNext()){
			Arc arc_g=arc_g_it.next();
			boolean has_larger=false;
			Iterator<Arc> arc_h_it=old2.getRight().iterator();
			while(arc_h_it.hasNext()){
				Arc arc_h=arc_h_it.next();
				if(arc_g.getFrom()==arc_h.getFrom()){
					if(!arc_g.getLabel()||arc_h.getLabel()){
						if(rel_spec.contains(new Pair<FAState,FAState>(new FAState(arc_g.getTo(),spec),new FAState(arc_h.getTo(),spec)))){
							has_larger=true;
							break;
						}
					}
				}
			}			
			if(!has_larger){
				return false;
			}
		}
		return true;
	}
	public void inclusionTest(){
		this.computeSim();
		if(quotient){
			spec=quotient(spec, rel_spec);
			system=quotient(system, rel_system);
			System.out.println("Aut A (quotiented): # of Trans. "+system.trans+", # of States "+system.states.size()+".");
			System.out.println("Aut B (quotiented): # of Trans. "+spec.trans+", # of States "+spec.states.size()+".");
		}
		debug("Spec.:");
		debug(spec.toString());
		debug("Sim="+showSim(rel_spec));
		debug("System:");
		debug(system.toString());
		debug("Sim="+showSim(rel_system));
		this.included=included();
		
	}
	public long getCpuTime( ) {
	    ThreadMXBean bean = ManagementFactory.getThreadMXBean( );
	    return bean.isCurrentThreadCpuTimeSupported( ) ?
	        bean.getCurrentThreadCpuTime( ) : 0L;
	}
	
	public boolean isIncluded(){
		return included;
	}
	@Override
	public void run(){

		runTime=getCpuTime();
			inclusionTest();
		runTime=getCpuTime()-runTime;
	}
	
	public long getRunTime(){
		return runTime;
	}


	void computeSim(){

		FAState[] states=spec.states.toArray(new FAState[0]);		
		boolean[] isFinal = new boolean[states.length];
		boolean[][] fsim = new boolean[states.length][states.length];
		// sim[u][v]=true iff v in sim(u) iff v simulates u
		
		for(int i=0;i<states.length;i++){			
			isFinal[i] = spec.F.contains(states[i]);
		}
		for(int i=0;i<states.length;i++){
			for(int j=i;j<states.length;j++){
				fsim[i][j] = (!isFinal[i] || isFinal[j]) && states[j].fw_covers(states[i]);
				fsim[j][i] = (isFinal[i] || !isFinal[j]) && states[i].fw_covers(states[j]);
			}
		}
		Simulation sim = new Simulation();
		rel_spec = sim.FastFSimRelNBW(spec,fsim);

		states=system.states.toArray(new FAState[0]);		
		isFinal = new boolean[states.length];
		fsim = new boolean[states.length][states.length];
		
		for(int i=0;i<states.length;i++){			
			isFinal[i] = system.F.contains(states[i]);
		}
		for(int i=0;i<states.length;i++){
			for(int j=i;j<states.length;j++){
				fsim[i][j] = (!isFinal[i] || isFinal[j]) && states[j].fw_covers(states[i]);
				fsim[j][i] = (isFinal[i] || !isFinal[j]) && states[i].fw_covers(states[j]);
			}
		}
		sim = new Simulation();
		rel_system = sim.FastFSimRelNBW(system,fsim);
		
	}	
	
	private boolean included(){
		
		ArrayList<Pair<Arc, TreeSet<Arc>>> Q1=this.buildSingleCharacterSuperGraphs();
		Iterator<Pair<Arc, TreeSet<Arc>>> Q1_it=Q1.iterator();
		while(Q1_it.hasNext()){
			Pair<Arc, TreeSet<Arc>> g=Q1_it.next();
			if(!double_graph_test(g, g, spec.getInitialState().id)){
				return false;
			}
		}
		TreeSet<Pair<Arc, TreeSet<Arc>>> Next=new TreeSet<Pair<Arc, TreeSet<Arc>>>(new SuperGraphComparator());
		TreeSet<Pair<Arc, TreeSet<Arc>>> Processed=new TreeSet<Pair<Arc, TreeSet<Arc>>>(new SuperGraphComparator());
		Next.addAll(Q1);
		while(!Next.isEmpty()){
			if(stop)
				break;
			
			Pair<Arc, TreeSet<Arc>> g=Next.first();
			Iterator<Pair<Arc, TreeSet<Arc>>> Processed_it=Processed.iterator();
			while(Processed_it.hasNext()){
				Pair<Arc, TreeSet<Arc>> h=Processed_it.next();
				if(!double_graph_test(g, h, spec.getInitialState().id)||!double_graph_test(h, g, spec.getInitialState().id))
					return false;
			}
			Next.remove(g);
			Processed.add(g);
			debug("Processed:"+Processed);
			debug("Next:"+Next);
			
			Q1_it=Q1.iterator();
			while(Q1_it.hasNext()){
				ArrayList<Pair<Arc, TreeSet<Arc>>> toRemove=new ArrayList<Pair<Arc, TreeSet<Arc>>>();
				Pair<Arc, TreeSet<Arc>> h=Q1_it.next();
				if(composable(g,h)){
				Pair<Arc, TreeSet<Arc>> f=compose(g, h);
				boolean discard=false;

				debug("f:"+f +"="+g+";"+h);
				
				Processed_it=Processed.iterator();
				while(Processed_it.hasNext()){
					Pair<Arc, TreeSet<Arc>> p=Processed_it.next();
					if(smallerThan(f, p)){
						toRemove.add(p);
					}
					if(smallerThan(p, f)){
						discard=true;
						break;
					}
				}
				if(discard)
					continue;
				Iterator<Pair<Arc, TreeSet<Arc>>> Next_it=Next.iterator();
				while(Next_it.hasNext()){
					Pair<Arc, TreeSet<Arc>> p=Next_it.next();
					if(smallerThan(f, p)){
						toRemove.add(p);
					}
					if(smallerThan(p, f)){
						discard=true;
						break;
					}
				}
				if(discard)
					continue;
				if(!double_graph_test(f, f, spec.getInitialState().id))
					return false;
				Processed.removeAll(toRemove);
				Next.removeAll(toRemove);
				if(opt2)
					Next.add(min(f));
				else
					Next.add(f);
				}
			}
		}			
		return true;
	}

	private boolean composable(Pair<Arc, TreeSet<Arc>> g,
			Pair<Arc, TreeSet<Arc>> h) {
		if(g.getLeft().getTo()==h.getLeft().getFrom())
			return true;
		else
			return false;
	}
	public void stopIt(){
		stop=true;
	}
}

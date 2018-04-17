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
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;
import comparator.SuperGraphComparator;
import datastructure.Arc;
import datastructure.OneToOneTreeMap;
import datastructure.Pair;



/**
 * 
 * @author Yu-Fang Chen
 * 
 */
public class InclusionAnti{
	boolean debug=false;
	public int removedCnt;
	static public int sggen=0;
	public boolean included=true;
	private TreeMap<String,TreeSet<Integer>> Tail=new TreeMap<String,TreeSet<Integer>>();
	private TreeMap<String,TreeSet<Integer>> Head=new TreeMap<String,TreeSet<Integer>>();
	private long runTime;
	private boolean stop=false;
	FiniteAutomaton spec, system;

	void debug(String out){
		if(debug)
		System.out.println(out);
	}
	public InclusionAnti(FiniteAutomaton system, FiniteAutomaton spec){
		this.spec=spec;
		this.system=system;
	}
	private boolean double_graph_test(Pair<Arc,TreeSet<Arc>> g, Pair<Arc,TreeSet<Arc>> h, int init){
		Arc g_arc=g.getLeft();
		Arc h_arc=h.getLeft();
		if(!(g_arc.getTo()==h_arc.getFrom() && h_arc.getTo()==h_arc.getFrom() &&
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
				old_arc.getTo()==old2_arc.getTo()))
			return false;
		
		Iterator<Arc> arc_g_it=old.getRight().iterator();
		while(arc_g_it.hasNext()){
			Arc arc_g=arc_g_it.next();
			boolean has_larger=false;
			Iterator<Arc> arc_h_it=old2.getRight().iterator();
			while(arc_h_it.hasNext()){
				Arc arc_h=arc_h_it.next();
				if(arc_g.getFrom()==arc_h.getFrom()){
					if(!arc_g.getLabel()||arc_h.getLabel()){
						if(arc_g.getTo()==arc_h.getTo()){
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
		debug("Spec.:");
		debug(spec.toString());
		debug("System:");
		debug(system.toString());
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
	public void run(){

		runTime=getCpuTime();
			inclusionTest();
		runTime=getCpuTime()-runTime;
	}
	
	public long getRunTime(){
		return runTime;
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
		sggen+=Q1.size();
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
					sggen++;
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

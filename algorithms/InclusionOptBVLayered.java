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
import java.lang.Math;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;
import comparator.StatePairComparator;
import datastructure.Arc;
import datastructure.Graph;
import datastructure.HashSet;
import datastructure.MetagraphBV;


import datastructure.NewMetagraph;
import datastructure.OneToOneTreeMap;
import datastructure.Pair;

/**
 * 
 * @author Richard Mayr, Yu-Fang Chen
 * 
 */
public class InclusionOptBVLayered {

	private int verbose = 10;
	int verboseC1 = 1;
	int verboseMin = 1;

	public int removedCnt;
	public boolean included = true;
        public String counterexample_prefix = "";  // These will record the counterexample, if not included.
        public String counterexample_loop = "";
        public boolean timeout=false;
	public int cntL = 0;

	private TreeMap<Graph, BitSet> SysTail = new TreeMap<Graph, BitSet>();
	private TreeMap<Graph, BitSet> SysHead = new TreeMap<Graph, BitSet>();

	private TreeMap<Graph, BitSet> SpecTail = new TreeMap<Graph, BitSet>();
	private TreeMap<Graph, BitSet> SpecHead = new TreeMap<Graph, BitSet>();

        private long runTime;
	private boolean stop = false;
    private Set<Pair<FAState, FAState>> frel, brel; 
	private Map<FAState, Set<FAState>> frelM, brelM;
	FiniteAutomaton spec, system;
        int limit;

	String showSim(Set<Pair<FAState, FAState>> sim) {
		String result = "";
		Iterator<Pair<FAState, FAState>> sim_it = sim.iterator();
		while (sim_it.hasNext()) {
			Pair<FAState, FAState> p = sim_it.next();
			if (p.getLeft().compareTo(p.getRight()) != 0)
				result += ("(" + p.getLeft() + "," + p.getRight() + ")");
		}
		return result;
	}

	void debug(String out, int v) {
		if (Options.debug && v > verbose)
			System.out.println(out);
	}

    public InclusionOptBVLayered(FiniteAutomaton system, FiniteAutomaton spec, int limit) {
		this.spec = spec;
		this.system = system;
		this.limit = limit;
	}

	private boolean C1(Arc left, Graph right) {
		if (!Options.C1) {
			return false;
		}
		if (left.getFrom() != system.getInitialState().id) {
			debug("C1(" + left + "," + right + ")=" + true, verboseC1);
			return true;
		}

		Iterator<Integer> leftSt_it = right.leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> right_it = right.iterator(leftSt_it.next());
			while (right_it.hasNext()) {
				Arc r = right_it.next();
				if (r.getFrom() == spec.getInitialState().id) {
					if (frelM.get(new FAState(left.getTo(), system))
							.contains(new FAState(r.getTo(), spec))) {
						debug("C1(" + left + "," + right + ")=" + true,
								verboseC1);
						return true;
					}
				}
			}
		}
		debug("C1(" + left + "," + right + ")=" + false, verboseC1);
		return false;
	}

	private boolean double_graph_test(MetagraphBV hl, MetagraphBV gr) {
		if (hl.getLeft().intersects(gr.getLeft())
				&& !hl.getRight().intersects(gr.getRight())) {
		    // System.out.println("DGT failed with rpstrings: "+hl.rpstring+" and "+gr.rpstring);
			return false;
		} else
			return true;
	}

	private BitSet getL(Graph g, int init, boolean isSpec/* spec takes upward */) {

		if (!(isSpec && SpecHead.containsKey(g))
				&& !(!isSpec && SysHead.containsKey(g))) {
			BitSet H = new BitSet();

			Iterator<Integer> leftSt_it = g.leftStateIt();
			while (leftSt_it.hasNext()) {
				Iterator<Arc> arc_g_it = g.iterator(leftSt_it.next());
				while (arc_g_it.hasNext()) {
					Arc arc_g = arc_g_it.next();
					if ((arc_g.L || isSpec/* arcs in spec do not have label */)
							&& arc_g.getFrom() == init) {
						H.set(arc_g.getTo());
					}

				}
			}
			boolean changed = true;
			while (changed) {
				changed = false;
				if (isSpec) {
					Iterator<Pair<FAState, FAState>> brel_it = brel.iterator();
					while (brel_it.hasNext()) {
						Pair<FAState, FAState> p = brel_it.next();
						if (p.getLeft().getowner() == spec
								&& p.getRight().getowner() == spec) {
							if (H.get(p.getLeft().id)
									&& !H.get(p.getRight().id)) {
								H.set(p.getRight().id);
								changed = true;
							}
						}
					}
				} else {
					Iterator<Pair<FAState, FAState>> frel_it = frel.iterator();
					while (frel_it.hasNext()) {
						Pair<FAState, FAState> p = frel_it.next();
						if (p.getLeft().getowner() == system
								&& p.getRight().getowner() == system) {
							if (H.get(p.getRight().id)
									&& !H.get(p.getLeft().id)) {
								H.set(p.getLeft().id);
								changed = true;
							}
						}
					}
				}
			}
			if (isSpec)
				SpecHead.put(g.clone(), H);
			else
				SysHead.put(g.clone(), H);
		}
		if (isSpec)
			return SpecHead.get(g);
		else
			return SysHead.get(g);
	}

	private BitSet getR(Graph h, boolean isSystem) {
		if (!(isSystem && SysTail.containsKey(h) && !(!isSystem && SpecTail
				.containsKey(h)))) {
			FiniteAutomaton fa = new FiniteAutomaton();
			OneToOneTreeMap<Integer, automata.FAState> st = new OneToOneTreeMap<Integer, automata.FAState>();

			Iterator<Integer> leftSt_it = h.leftStateIt();
			while (leftSt_it.hasNext()) {
				Iterator<Arc> arc_h_it = h.iterator(leftSt_it.next());
				while (arc_h_it.hasNext()) {
					Arc arc_h = arc_h_it.next();
					if (!st.containsKey(arc_h.getFrom()))
						st.put(arc_h.getFrom(), fa.createState());
					if (!st.containsKey(arc_h.getTo()))
						st.put(arc_h.getTo(), fa.createState());
					fa.addTransition(st.getValue(arc_h.getFrom()), st
							.getValue(arc_h.getTo()),
							arc_h.getLabel() ? "1" : "0");
				}
			}
			if (!isSystem && Options.backward) {
				Iterator<Pair<FAState, FAState>> brel_it = brel.iterator();
				while (brel_it.hasNext()) {
					Pair<FAState, FAState> p = brel_it.next();
					if ((p.getLeft().getowner() == spec && p.getRight()
							.getowner() == spec)) {
						if (!st.containsKey(p.getLeft().getID()))
							st.put(p.getLeft().getID(), fa.createState());
						if (!st.containsKey(p.getRight().getID()))
							st.put(p.getRight().getID(), fa.createState());
						fa.addTransition(st.getValue(p.getLeft().getID()),
								st.getValue(p.getRight().getID()), "0");
					}
				}
			}
			if (isSystem) {
				Iterator<Pair<FAState, FAState>> frel_it = frel.iterator();
				while (frel_it.hasNext()) {
					Pair<FAState, FAState> p = frel_it.next();
					if ((p.getLeft().getowner() == system && p.getRight()
							.getowner() == system)) {
						if (!st.containsKey(p.getLeft().getID()))
							st.put(p.getLeft().getID(), fa.createState());
						if (!st.containsKey(p.getRight().getID()))
							st.put(p.getRight().getID(), fa.createState());
						fa.addTransition(st.getValue(p.getRight().getID()),
								st.getValue(p.getLeft().getID()), "0");
					}
				}
			}
			SCC s = new SCC(fa);
			BitSet T = new BitSet();
			Iterator<FAState> s_it = s.getResult().iterator();
			while (s_it.hasNext()) {
				T.set(st.getKey(s_it.next()));
			}
			Graph isolatedArcs = new Graph();
			isolatedArcs.addAll(h);

			if (!isSystem && Options.backward) {
				Iterator<Pair<FAState, FAState>> brel_it = brel.iterator();
				while (brel_it.hasNext()) {
					Pair<FAState, FAState> p = brel_it.next();
					if ((p.getLeft().getowner() == spec && p.getRight()
							.getowner() == spec)) {
						isolatedArcs.add(new Arc(p.getLeft().id, false, p
								.getRight().id));
					}
				}
			}
			if (isSystem) {
				Iterator<Pair<FAState, FAState>> frel_it = frel.iterator();
				while (frel_it.hasNext()) {
					Pair<FAState, FAState> p = frel_it.next();
					if ((p.getLeft().getowner() == system && p.getRight()
							.getowner() == system)) {
						isolatedArcs.add(new Arc(p.getRight().id, false, p
								.getLeft().id));
					}
				}
			}

			boolean changed = true;
			while (changed) {
				changed = false;
				Graph isolatedArcsTemp = new Graph();
				Iterator<Integer> left_it = isolatedArcs.leftStateIt();
				while (left_it.hasNext()) {
					Iterator<Arc> arc_it = isolatedArcs.iterator(left_it
							.next());
					while (arc_it.hasNext()) {
						Arc arc = arc_it.next();
						if (!T.get(arc.getTo())) {
							isolatedArcsTemp.add(arc);
						} else {
							changed = true;
							T.set(arc.getFrom());
						}
					}
				}
				isolatedArcs = isolatedArcsTemp;
			}
			if (isSystem)
				SysTail.put(h, T);
			else
				SpecTail.put(h, T);
		}
		if (isSystem)
			return SysTail.get(h);
		else
			return SpecTail.get(h);
	}


	private boolean leftSubsume(Arc cur, Arc other) {
		if (cur.getFrom() == other.getFrom()) {
			if (!cur.getLabel() || other.getLabel()) {
				if (cur.getTo() != other.getTo()) {
					if (frelM.get(new FAState(cur.getTo(), system)).contains(
							new FAState(other.getTo(), system))) {
						if (!frelM.get(new FAState(other.getTo(), system))
								.contains(new FAState(cur.getTo(), system))) {
							return true;
						} else if (cur.getTo() < other.getTo()) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	private boolean rightSubsume(Arc cur, Arc other, boolean l) {
		if (l
				|| brelM.get(new FAState(cur.getFrom(), spec)).contains(
						new FAState(other.getFrom(), spec))) {
			if (other.getFrom() >= cur.getFrom()
					|| !brelM.get(new FAState(other.getFrom(), spec)).contains(
							new FAState(cur.getFrom(), spec))) {
				if (!cur.getLabel() || other.getLabel()) {
					if (frelM.get(new FAState(cur.getTo(), spec)).contains(
							new FAState(other.getTo(), spec))) {
						if (other.getTo() >= cur.getTo()
								|| !frelM.get(new FAState(other.getTo(), spec))
										.contains(
												new FAState(cur.getTo(), spec))) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	private NewMetagraph min_plus(NewMetagraph NewMetagraph) {
		debug("before min:" + NewMetagraph, verboseMin);
		Graph left_result = new Graph();
		Iterator<Integer> leftSt_it = NewMetagraph.getLeft().leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> arc_it1 = NewMetagraph.getLeft().iterator(
					leftSt_it.next());
			while (arc_it1.hasNext()) {
				Arc cur = arc_it1.next();
				boolean canAdd = true;
				if(cur.L){
					cntL--;
				}

				Iterator<Arc> arc_it2 = NewMetagraph.getLeft().iterator(
						cur.getFrom());
				while (arc_it2.hasNext()) {
					Arc other = arc_it2.next();
					if (leftSubsume(cur, other)) {
						canAdd = false;
						break;
					}
				}
				if (canAdd) {
					left_result.add(cur);
					if(cur.L){
						cntL++;
					}
				}
			}
		}

		Graph right_result = new Graph();
		leftSt_it = NewMetagraph.getRight().leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> arc_it1 = NewMetagraph.getRight().iterator(
					leftSt_it.next());
			while (arc_it1.hasNext()) {
				Arc cur = arc_it1.next();
				boolean canAdd = true;
				Iterator<FAState> bwLgSts_it = brelM.get(
						new FAState(cur.getFrom(), spec)).iterator();
				while (bwLgSts_it.hasNext()) {
					FAState bwLgSt = bwLgSts_it.next();
					if (bwLgSt.getowner() != spec)
						continue;

					Iterator<Arc> arc_it2 = NewMetagraph.getRight()
							.iterator(bwLgSt.getID());
					while (arc_it2.hasNext()) {
						Arc other = arc_it2.next();
						if (cur.getFrom() == other.getFrom()
								&& cur.getTo() == other.getTo())
							continue;
						if (rightSubsume(cur, other, true)) {
							canAdd = false;
							break;
						}
					}
					if (!canAdd)
						break;
				}
				if (canAdd) {
					right_result.add(cur);
				}
			}
		}
		debug("after min:" + new Pair<Graph, Graph>(left_result, right_result),
				verboseMin);
		return new NewMetagraph(left_result, right_result,
				NewMetagraph.rpstring);
	}


	private ArrayList<NewMetagraph> buildSingleCharacterNewMetagraphs() {
		ArrayList<NewMetagraph> NewMetagraphs = new ArrayList<NewMetagraph>();
		Iterator<String> symbol_it = system.getAllTransitionSymbols()
				.iterator();
		while (symbol_it.hasNext()) {
			Graph rightGraph = new Graph();
			String sym = symbol_it.next();
			Iterator<FAState> from_it = spec.states.iterator();
			while (from_it.hasNext()) {
				FAState from = from_it.next();
				if (from.getNext(sym) != null) {
					Iterator<FAState> to_it = from.getNext(sym).iterator();
					while (to_it.hasNext()) {
						FAState to = to_it.next();
						if (spec.F.contains(from) || spec.F.contains(to)) {
							rightGraph.add(new Arc(from.id, true, to.id));
						} else {
							rightGraph.add(new Arc(from.id, false, to.id));
						}
					}
				}
			}

			Graph leftGraph = new Graph();
			from_it = system.states.iterator();
			while (from_it.hasNext()) {
				FAState from = from_it.next();
				if (from.getNext(sym) != null) {
					Iterator<FAState> to_it = from.getNext(sym).iterator();
					while (to_it.hasNext()) {
						FAState to = to_it.next();
						if (system.F.contains(from) || system.F.contains(to)) {
							leftGraph.add(new Arc(from.id, true, to.id));
						} else {
							leftGraph.add(new Arc(from.id, false, to.id));
						}
					}
				}
			}
			NewMetagraph f = min_plus(new NewMetagraph(leftGraph, rightGraph));
			f.rpstring = sym;

			ArrayList<NewMetagraph> toRemove = new ArrayList<NewMetagraph>();
			ArrayList<NewMetagraph> toAdd = new ArrayList<NewMetagraph>();

			Iterator<NewMetagraph> NewMetagraph_it = NewMetagraphs.iterator();
			while (NewMetagraph_it.hasNext()) {
				NewMetagraph p = NewMetagraph_it.next();
				cleanLayered(f, p, (short) 1);
				if (f.getLeft().size() == 0)
					break;

				Graph left = new Graph();
				left.addAll(p.getLeft());
				Graph right = new Graph();
				right.addAll(p.getRight());
				NewMetagraph p_new = new NewMetagraph(left, right, p.rpstring);
				
				boolean changed=cleanLayered(p_new, f, (short) 3);
				if (changed) {
					toRemove.add(p);
					if (p_new.getLeft().size() > 0)
						toAdd.add(p_new);
				}
			}
			if (f.getLeft().size() != 0) {
				NewMetagraphs.add(f);
				NewMetagraphs.removeAll(toRemove);
				NewMetagraphs.addAll(toAdd);
			}
		}

		Iterator<NewMetagraph> Q1_it = NewMetagraphs.iterator();
		while (Q1_it.hasNext()) {
			NewMetagraph g = Q1_it.next();
			Iterator<Integer> leftSt_it = g.getLeft().leftStateIt();
			while (leftSt_it.hasNext()) {
				Iterator<Arc> left_it = g.getLeft().iterator(
						leftSt_it.next());
				while (left_it.hasNext()) {
					Arc left = left_it.next();
					boolean c1 = C1(left, g.getRight());
					if (!c1) {
						left.L = true;
						cntL++;
					}
				}
			}
		}
		return NewMetagraphs;
	}
	

	private void labelArc(boolean C1, boolean LLabeled, Arc arc, Graph right) {
		arc.R = true;
		if (C1) {
			if (LLabeled) {
				if (!C1(arc, right)) {
					arc.L = true;
					debug("Add L label to " + arc, verboseC1);
				}
			}
		} else {
			arc.L = true;
			debug("Add L label to " + arc, verboseC1);
		}
	}

	private NewMetagraph compose(NewMetagraph g, NewMetagraph h, Graph oriL) {
		Graph right = new Graph();
		Iterator<Integer> leftSt_it = g.getRight().leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> arc_g_it = g.getRight()
					.iterator(leftSt_it.next());
			while (arc_g_it.hasNext()) {
				Arc arc_g = arc_g_it.next();
				Iterator<FAState> bwLgSts_it = brelM.get(
						new FAState(arc_g.getTo(), spec)).iterator();
				while (bwLgSts_it.hasNext()) {
					FAState bwLgSt = bwLgSts_it.next();
					if (bwLgSt.getowner() != spec)
						continue;
					Iterator<Arc> arc_h_it = h.getRight().iterator(
							bwLgSt.getID());
					while (arc_h_it.hasNext()) {
						Arc arc_h = arc_h_it.next();
						if (arc_g.getLabel() || arc_h.getLabel()) {
							right.add(new Arc(arc_g.getFrom(), true, arc_h
									.getTo()));
							right.remove(new Arc(arc_g.getFrom(), false,
									arc_h.getTo()));
						} else {
							if (!right.contains(new Arc(arc_g.getFrom(),
									true, arc_h.getTo()))) {
								right.add(new Arc(arc_g.getFrom(), false,
										arc_h.getTo()));
							}
						}
					}
				}
			}
		}
		Graph left = new Graph();
		leftSt_it = g.getLeft().leftStateIt();
		while (leftSt_it.hasNext()) {
			int leftSt = leftSt_it.next();
			Iterator<Arc> arc_i_it = g.getLeft().iterator(leftSt);
			while (arc_i_it.hasNext()) {
				Arc arc_i = arc_i_it.next();
				boolean LLabeled = oriL.contains(arc_i);
				Iterator<Arc> arc_h_it = h.getLeft()
						.iterator(arc_i.getTo());
				if (arc_h_it != null) {
					while (arc_h_it.hasNext()) {
						Arc arc_h = arc_h_it.next();
						if (arc_i.getLabel() || arc_h.getLabel()) {
							Arc newarc = new Arc(arc_i.getFrom(), true,
									arc_h.getTo());
							Arc oldarc = new Arc(arc_i.getFrom(), false,
									arc_h.getTo());
							labelArc(Options.C1, LLabeled, newarc, right);
							oldarc.L=newarc.L;
							if(!left.contains(newarc)){
								left.add(newarc);
								
								if(left.contains(oldarc)){
									left.remove(new Arc(arc_i.getFrom(), false,
									arc_h.getTo()));
								}else if(newarc.L){
									cntL++;
								}
							}
						} else {
							Arc newarc = new Arc(arc_i.getFrom(), false,
									arc_h.getTo());
							Arc oldarc = new Arc(arc_i.getFrom(), true,
									arc_h.getTo());
							labelArc(Options.C1, LLabeled, newarc,
									right);
							oldarc.L=newarc.L;
							if (!left.contains(oldarc)) {
								left.add(newarc);
								if(newarc.L)
									cntL++;
							}
						}
					}
				}
			}
		}
		if (left.size() == 0) {
			return null;
		} else {
			return new NewMetagraph(left, right, g.rpstring + h.rpstring);
		}
	}



	
    // We test if at least one A-arc in src would be removed, if subsumption held for the B-graphs
	private boolean cleanPretest(NewMetagraph src, NewMetagraph tgt){
	    // If A part too large then we don't hope for an efficient pre-test. Constant 4 is found empirically.
        if(src.getLeft().size() > tgt.getRight().size()/4) return true;

        Iterator<Integer> leftSt_it = src.getLeft().leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> arc_g_it = src.getLeft().iterator(leftSt_it.next());
			while (arc_g_it.hasNext()) {
				Arc arc_g = arc_g_it.next();//enumerate arcs in left graph of src
				Iterator<Arc> arc_h_it = tgt.getLeft().iterator(arc_g.getFrom());
				Arc arc_h = null;
				while (arc_h_it.hasNext()) {
					arc_h = arc_h_it.next();
					if (!arc_g.getLabel() || arc_h.getLabel()) {
						if (myfsim2[arc_g.getTo()][arc_h.getTo()]) {
						    return true;
						}
					}
				}
			}
		}
		return false;
	}
    
	// clean NewMetagraph src w.r.t tgt	// if tgt.right not smaller than src.right then does nothing
	boolean cleanLayered(NewMetagraph src, NewMetagraph tgt, short type) {
	    if(Options.CPT) { if (!cleanPretest(src,tgt)) return false; }

		boolean changed=false;
		Iterator<Integer> leftSt_it = tgt.getRight().leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> arc_g_it = tgt.getRight().iterator(leftSt_it.next());
			while (arc_g_it.hasNext()) {
				Arc arc_g = arc_g_it.next();//enumerate arcs in right graph of tgt
				boolean has_larger = false;
				Iterator<FAState> bwLgSts_it = brelM.get(
						new FAState(arc_g.getFrom(), spec)).iterator();
				while (bwLgSts_it.hasNext()) {
					FAState bwLgSt = bwLgSts_it.next();
					if (bwLgSt.getowner() != spec)
						continue;
					Iterator<Arc> arc_h_it = src.getRight().iterator(
							bwLgSt.getID());

					while (arc_h_it.hasNext()) {
						Arc arc_h = arc_h_it.next();
						if (!arc_g.getLabel() || arc_h.getLabel()) {
							if (myfsim[arc_g.getTo()][arc_h.getTo()]) {
								has_larger = true;
								break;
							}
						}
					}
					if (has_larger)
						break;
				}

				if (!has_larger) {
					return changed;
				}
			}
		}
		debug("Before clean" + type + " :" + src + " (w.r.t. " + tgt + ")", 100);
		// tgt.right smaller than src.right
		if (type != 3 && src.getRight().size() == tgt.getRight().size()) {
			boolean has_larger = false;
			leftSt_it = src.getRight().leftStateIt();
			while (leftSt_it.hasNext()) {
				int leftSt = leftSt_it.next();
				Iterator<Arc> arc_g_it = src.getRight().iterator(leftSt);//enumerate arcs in right graph of src
				while (arc_g_it.hasNext()) {
					Arc arc_g = arc_g_it.next();
					has_larger = false;
					Iterator<FAState> bwLgSts_it = brelM.get(
							new FAState(arc_g.getFrom(), spec)).iterator();
					while (bwLgSts_it.hasNext()) {
						FAState bwLgSt = bwLgSts_it.next();
						if (bwLgSt.getowner() != spec)
							continue;
						Iterator<Arc> arc_h_it = tgt.getRight().iterator(
								bwLgSt.getID());
						while (arc_h_it.hasNext()) {
							Arc arc_h = arc_h_it.next();
							if (!arc_g.getLabel() || arc_h.getLabel()) {
								if (myfsim[arc_g.getTo()][arc_h.getTo()]
								// frelM.get(new
								// FAState(arc_g.getTo(),spec)).contains(new
								// FAState(arc_h.getTo(),spec))
								) {
									has_larger = true;
									break;
								}
							}
						}
						if (has_larger)
							break;
					}
					if (!has_larger)
						break;
				}
				if (!has_larger)
					break;
			}
			if (has_larger) {
				changed=true;
				src.getRight().clear();
				src.getRight().addAll(tgt.getRight());
			}
		}
		boolean regain = false;
		Graph left = new Graph();

		leftSt_it = src.getLeft().leftStateIt();
		while (leftSt_it.hasNext()) {
			Iterator<Arc> arc_g_it = src.getLeft().iterator(leftSt_it.next());
			while (arc_g_it.hasNext()) {
				Arc arc_g = arc_g_it.next();//enumerate arcs in left graph of src
				if(arc_g.L)
					cntL--;
				boolean has_larger = false;
				Iterator<Arc> arc_h_it = tgt.getLeft()
						.iterator(arc_g.getFrom());
				Arc arc_h = null;
				while (arc_h_it.hasNext()) {
					arc_h = arc_h_it.next();
					if (!arc_g.getLabel() || arc_h.getLabel()) {
						if (myfsim2[arc_g.getTo()][arc_h.getTo()]
						) {
							has_larger = true;
							changed=true;
							break;
						}
					}
				}
				if (!has_larger) {
					left.add(arc_g);
					if(arc_g.L)
						cntL++;
				} else if (type == 2) {
					if (arc_g.L) {
						if(!arc_h.L){
							arc_h.L = true;
							cntL++;
						}
						regain = true;
					}
				}
			}
		}
		src.getLeft().clear();
		src.getLeft().addAll(left);
		debug("After clean" + type + " :" + src, 100);
		if (regain)
			debug("Regain L :" + tgt, 100);
		return changed;

	}

	boolean smallerThan(Pair<Arc, Graph> old, Pair<Arc, Graph> old2) {
		Arc old_arc = old.getLeft();
		Arc old2_arc = old2.getLeft();
		if (!(old_arc.getFrom() == old2_arc.getFrom()
				&& (old_arc.getLabel() || !old2_arc.getLabel()) && frelM.get(
				new FAState(old2_arc.getTo(), system)).contains(
				new FAState(old_arc.getTo(), system)))) {
			return false;
		}
		Iterator<Integer> leftSt_it = old.getRight().leftStateIt();
		while (leftSt_it.hasNext()) {
			int leftSt = leftSt_it.next();
			Iterator<Arc> arc_g_it = old.getRight().iterator(leftSt);
			while (arc_g_it.hasNext()) {
				Arc arc_g = arc_g_it.next();
				boolean has_larger = false;
				Iterator<FAState> bwLgSts_it = brelM.get(
						new FAState(arc_g.getFrom(), spec)).iterator();
				while (bwLgSts_it.hasNext()) {
					FAState bwLgSt = bwLgSts_it.next();
					if (bwLgSt.getowner() != spec)
						continue;
					Iterator<Arc> arc_h_it = old2.getRight().iterator(
							bwLgSt.getID());
					while (arc_h_it.hasNext()) {
						Arc arc_h = arc_h_it.next();
						if (!arc_g.getLabel() || arc_h.getLabel()) {
							if (frelM
									.get(new FAState(arc_g.getTo(), spec))
									.contains(
											new FAState(arc_h.getTo(), spec))) {
								has_larger = true;
								break;
							}
						}
					}
				}
				if (!has_larger) {
					return false;
				}
			}
		}
		return true;
	}

	public boolean[][] myfsim;
	public boolean[][] myfsim2;

	public void inclusionTest() {

	    Simulation sim2 = new Simulation();
	    Minimization Minimizer = new Minimization();

	    // Compute simulation relations for subsumption.
	    // Only use lookahead simulation if option blasub given AND no limit specified (i.e., limit==0).
	    // The lightweight version with limit >0 must not use the heavy lookahead simulation!
		if(Options.blasub && limit==0){
		    frel=sim2.BLASimRelNBW(system, spec, Minimizer.lookahead(system,spec));
		    if (Options.C1 && frel.contains(new Pair<FAState, FAState>(system.getInitialState(), spec.getInitialState()))) {
			return; };
		    brel=sim2.BLABSimRelNBW(system, spec, Minimizer.lookahead(system,spec));
		    brelM = new TreeMap<FAState, Set<FAState>>();
		    Iterator<Pair<FAState, FAState>> brel_it = brel.iterator();
			while (brel_it.hasNext()) {
				Pair<FAState, FAState> rel = brel_it.next();
				if (!brelM.containsKey(rel.getLeft())) {
					Set<FAState> sts = new TreeSet<FAState>();
					brelM.put(rel.getLeft(), sts);
				}
				brelM.get(rel.getLeft()).add(rel.getRight());
			}

			frelM = new TreeMap<FAState, Set<FAState>>();
			    Iterator<Pair<FAState, FAState>> frel_it = frel.iterator();
				while (frel_it.hasNext()) {
				    Pair<FAState, FAState> rel = frel_it.next();
					if (!frelM.containsKey(rel.getLeft())) {
					    Set<FAState> sts = new TreeSet<FAState>();
						frelM.put(rel.getLeft(), sts);
						    }
					    frelM.get(rel.getLeft()).add(rel.getRight());
						}
		}
		else{
		    this.computeSim(true);
		    if (Options.C1 && frel.contains(new Pair<FAState, FAState>(system.getInitialState(), spec.getInitialState()))) {
			return; };
		}

		// Now get matrix for frel.
		int mydim = spec.states.size();
		myfsim = new boolean[mydim][mydim];
		for (int i = 0; i < mydim; i++)
			for (int j = 0; j < mydim; j++)
				myfsim[i][j] = false;
		int mydim2 = system.states.size();
		myfsim2 = new boolean[mydim2][mydim2];
		for (int i = 0; i < mydim2; i++)
			for (int j = 0; j < mydim2; j++)
				myfsim2[i][j] = false;

		Iterator<Pair<FAState, FAState>> frel_it = frel.iterator();
		while (frel_it.hasNext()) {
			Pair<FAState, FAState> rel = frel_it.next();
			if (rel.getLeft().getowner() == spec
					&& rel.getRight().getowner() == spec)
				myfsim[rel.getLeft().getID()][rel.getRight().getID()] = true;
			if (rel.getLeft().getowner() == system
					&& rel.getRight().getowner() == system)
				myfsim2[rel.getLeft().getID()][rel.getRight().getID()] = true;
		}

		/*
		debug("Aut A:", 100);
		debug(system.toString(), 100);
		debug("Aut B:", 100);
		debug(spec.toString(), 100);
		debug("FSim=" + showSim(frel), 100);
		if (Options.backward)
			debug("BSim=" + showSim(brel), 100);
		*/
		
		this.included = included();
	}

        public long getCpuTime() {
		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		return bean.isCurrentThreadCpuTimeSupported() ? bean
				.getCurrentThreadCpuTime() : 0L;
	}

	public boolean isIncluded() {
		return included;
	}

	public void run() {
		runTime = getCpuTime();
		inclusionTest();
		runTime = getCpuTime() - runTime;
	}

    	public long getRunTime() {
		return runTime;
	}


//	boolean computeSim2() {
//		int oldspec = spec.states.size();
//		int oldsys = system.states.size();
//
//		ArrayList<FAState> all_states = new ArrayList<FAState>();
//		HashSet<String> alphabet = new HashSet<String>();
//
//		all_states.addAll(spec.states);
//		alphabet.addAll(spec.alphabet);
//
//		all_states.addAll(system.states);
//		alphabet.addAll(system.alphabet);
//
//		boolean result = false;
//		FAState[] states = all_states.toArray(new FAState[0]);
//		boolean[] isFinal = new boolean[states.length];
//		boolean[] isInit = new boolean[states.length];
//		boolean[][] fsim = new boolean[states.length][states.length];
//		boolean[][] bsim = new boolean[states.length][states.length];
//		for (int i = 0; i < states.length; i++) {
//			isFinal[i] = states[i].getowner().F.contains(states[i]);
//			isInit[i] = states[i].getowner().getInitialState()
//					.compareTo(states[i]) == 0;
//		}
//		for (int i = 0; i < states.length; i++) {
//			for (int j = i; j < states.length; j++) {
//				fsim[i][j] = (!isFinal[i] || isFinal[j])
//						&& states[j].fw_covers(states[i]);
//				fsim[j][i] = (isFinal[i] || !isFinal[j])
//						&& states[i].fw_covers(states[j]);
//				if (Options.backward) {
//					bsim[i][j] = (!isInit[i] || isInit[j])
//							&& (!isFinal[i] || isFinal[j])
//							&& states[j].bw_covers(states[i]);
//					bsim[j][i] = (isInit[i] || !isInit[j])
//							&& (isFinal[i] || !isFinal[j])
//							&& states[i].bw_covers(states[j]);
//				}
//			}
//		}
//		Simulation sim = new Simulation();
//		frel = sim.FastFSimRelNBW(spec, system, fsim);
//		if (Options.C1
//				&& frel.contains(new Pair<FAState, FAState>(system
//						.getInitialState(), spec.getInitialState()))) {
//			return true;
//		}
//
//		if (Options.fplus) {
//			Set<Pair<FAState, FAState>> temp = new TreeSet<Pair<FAState, FAState>>(
//					new StatePairComparator());
//			for (int i = 0; i < states.length; i++) {
//				for (int j = 0; j < states.length; j++) {
//					if (isFinal[i] && !isFinal[j]) {
//						Iterator<String> alphabet_it = states[i].nextIt();
//						boolean covered = true;
//						while (alphabet_it.hasNext()) {
//							String a = alphabet_it.next();
//							if (states[i].getNext(a) != null
//									&& states[j].getNext(a) == null) {
//								covered = false;
//								break;
//							}
//
//							Iterator<FAState> small_it = states[i].getNext(a)
//									.iterator();
//							while (small_it.hasNext()) {
//								FAState small = small_it.next();
//								covered = false;
//								if (states[j].getNext(a) != null) {
//									Iterator<FAState> big_it = states[j]
//											.getNext(a).iterator();
//									while (big_it.hasNext()) {
//										FAState big = big_it.next();
//										if (frel.contains(new Pair<FAState, FAState>(
//												small, big))
//												&& big.getowner().F
//														.contains(big)) {
//											covered = true;
//											break;
//										}
//									}
//								}
//								if (!covered)
//									break;
//							}
//							if (!covered)
//								break;
//						}
//						if (covered) {
//							temp.add(new Pair<FAState, FAState>(states[i],
//									states[j]));
//						}
//					}
//				}
//			}
//			frel.addAll(temp);
//		}
//		spec = quotient(spec, frel);
//		system = quotient(system, frel);
//		// frelM has to be recomputed
//		if (Options.backward) {
//			all_states.clear();
//			all_states.addAll(spec.states);
//			all_states.addAll(system.states);
//			states = all_states.toArray(new FAState[0]);
//			isFinal = new boolean[states.length];
//			isInit = new boolean[states.length];
//			bsim = new boolean[states.length][states.length];
//			for (int i = 0; i < states.length; i++) {
//				isFinal[i] = states[i].getowner().F.contains(states[i]);
//				isInit[i] = states[i].getowner().getInitialState()
//						.compareTo(states[i]) == 0;
//			}
//			for (int i = 0; i < states.length; i++) {
//				for (int j = i; j < states.length; j++) {
//					bsim[i][j] = (!isInit[i] || isInit[j])
//							&& (!isFinal[i] || isFinal[j])
//							&& states[j].bw_covers(states[i]);
//					bsim[j][i] = (isInit[i] || !isInit[j])
//							&& (isFinal[i] || !isFinal[j])
//							&& states[i].bw_covers(states[j]);
//				}
//			}
//			brel = sim.FastBSimRelNBW(spec, system, bsim);
//			spec = quotient(spec, brel);
//			system = quotient(system, brel);
//			// brelM has to be recomputed
//		}
//		if (oldspec > spec.states.size() || oldsys > system.states.size())
//			result = true;
//		return (result);
//	}


	void computeSim(boolean allow_fplus) {

		ArrayList<FAState> all_states = new ArrayList<FAState>();
		HashSet<String> alphabet = new HashSet<String>();

		all_states.addAll(spec.states);
		alphabet.addAll(spec.alphabet);

		all_states.addAll(system.states);
		alphabet.addAll(system.alphabet);

		FAState[] states = all_states.toArray(new FAState[0]);
		boolean[] isFinal = new boolean[states.length];
		boolean[] isInit = new boolean[states.length];
		boolean[][] fsim = new boolean[states.length][states.length];
		boolean[][] bsim = new boolean[states.length][states.length];
		// sim[u][v]=true iff v in sim(u) iff v simulates u
		for (int i = 0; i < states.length; i++) {
			isFinal[i] = states[i].getowner().F.contains(states[i]);
			isInit[i] = states[i].getowner().getInitialState()
					.compareTo(states[i]) == 0;
		}
		for (int i = 0; i < states.length; i++) {
			for (int j = i; j < states.length; j++) {
				fsim[i][j] = (!isFinal[i] || isFinal[j])
						&& states[j].fw_covers(states[i]);
				fsim[j][i] = (isFinal[i] || !isFinal[j])
						&& states[i].fw_covers(states[j]);
			}
		}
		Simulation sim = new Simulation();
		frel = sim.FastFSimRelNBW(spec, system, fsim);
		if (Options.C1) {
			if (frel.contains(new Pair<FAState, FAState>(system
					.getInitialState(), spec.getInitialState()))) {
				return;
			}
		}

		if (allow_fplus && Options.fplus) {
			Set<Pair<FAState, FAState>> temp = new TreeSet<Pair<FAState, FAState>>(
					new StatePairComparator());
			for (int i = 0; i < states.length; i++) {
				for (int j = 0; j < states.length; j++) {
					if (isFinal[i] && !isFinal[j]) {
						Iterator<String> alphabet_it = states[i].nextIt();
						boolean covered = true;
						while (alphabet_it.hasNext()) {
							String a = alphabet_it.next();
							if (states[i].getNext(a) != null
									&& states[j].getNext(a) == null) {
								covered = false;
								break;
							}

							Iterator<FAState> small_it = states[i].getNext(a)
									.iterator();
							while (small_it.hasNext()) {
								FAState small = small_it.next();
								covered = false;
								if (states[j].getNext(a) != null) {
									Iterator<FAState> big_it = states[j]
											.getNext(a).iterator();
									while (big_it.hasNext()) {
										FAState big = big_it.next();

										if (frel.contains(new Pair<FAState, FAState>(
												small, big))
												&& big.getowner().F
														.contains(big)) {
											covered = true;
											break;
										}
									}
								}
								if (!covered)
									break;
							}
							if (!covered)
								break;
						}
						if (covered) {
							temp.add(new Pair<FAState, FAState>(states[i],
									states[j]));
						}
					}
				}
			}
			frel.addAll(temp);
			if(Options.verbose && !temp.isEmpty()) System.out.println("Fplus: "+temp.size()+" pairs added.");
		}

		frelM = new TreeMap<FAState, Set<FAState>>();
		Iterator<Pair<FAState, FAState>> frel_it = frel.iterator();
		while (frel_it.hasNext()) {
			Pair<FAState, FAState> rel = frel_it.next();
			if (!frelM.containsKey(rel.getLeft())) {
				Set<FAState> sts = new TreeSet<FAState>();
				frelM.put(rel.getLeft(), sts);
			}
			frelM.get(rel.getLeft()).add(rel.getRight());
		}

		brelM = new TreeMap<FAState, Set<FAState>>();
		all_states.clear();
		all_states.addAll(spec.states);
		all_states.addAll(system.states);
		states = all_states.toArray(new FAState[0]);

		if (Options.backward) {
			isFinal = new boolean[states.length];
			isInit = new boolean[states.length];
			bsim = new boolean[states.length][states.length];
			for (int i = 0; i < states.length; i++) {
				isFinal[i] = states[i].getowner().F.contains(states[i]);
				isInit[i] = states[i].getowner().getInitialState()
						.compareTo(states[i]) == 0;
			}
			for (int i = 0; i < states.length; i++) {
				for (int j = i; j < states.length; j++) {
					bsim[i][j] = (!isInit[i] || isInit[j])
							&& (!isFinal[i] || isFinal[j])
							&& states[j].bw_covers(states[i]);
					bsim[j][i] = (isInit[i] || !isInit[j])
							&& (isFinal[i] || !isFinal[j])
							&& states[i].bw_covers(states[j]);
				}
			}
			brel = sim.FastBSimRelNBW(spec, system, bsim);
			Iterator<Pair<FAState, FAState>> brel_it = brel.iterator();
			while (brel_it.hasNext()) {
				Pair<FAState, FAState> rel = brel_it.next();
				if (!brelM.containsKey(rel.getLeft())) {
					Set<FAState> sts = new TreeSet<FAState>();
					brelM.put(rel.getLeft(), sts);
				}
				brelM.get(rel.getLeft()).add(rel.getRight());
			}
		} else {
			brel = new TreeSet<Pair<FAState, FAState>>(
					new StatePairComparator());
			for (int i = 0; i < states.length; i++) {
				Set<FAState> sts = new TreeSet<FAState>();
				sts.add(states[i]);
				brelM.put(states[i], sts);
				brel.add(new Pair<FAState, FAState>(states[i], states[i]));
			}
		}
	}


	public int mggen = 0;
	public int processed = 0;

	private boolean included() {
		ArrayList<NewMetagraph> Q1 = this.buildSingleCharacterNewMetagraphs();
		debug("Init:" + Q1, 100);

		Iterator<NewMetagraph> Q1_it = Q1.iterator();

		while (Q1_it.hasNext()) {
			NewMetagraph g = Q1_it.next();
			// System.out.println("Considering sc Metagraph with symbol: "+g.rpstring);
			if (!double_graph_test(
					new MetagraphBV(getL(g.getLeft(),
							     system.getInitialState().id, false), 
							getL(g.getRight(), 
							     spec.getInitialState().id, true), 
							g.rpstring),
					new MetagraphBV(getR(g.getLeft(), true), getR(g.getRight(), false), g.rpstring))) {
			    this.counterexample_prefix = g.rpstring;
			    this.counterexample_loop = g.rpstring;
				return false;
			}
		}

		LinkedList<NewMetagraph> Next = new LinkedList<NewMetagraph>();
		LinkedList<NewMetagraph> Processed = new LinkedList<NewMetagraph>();
		TreeSet<MetagraphBV> ProcessedL = new TreeSet<MetagraphBV>();
		TreeSet<MetagraphBV> ProcessedR = new TreeSet<MetagraphBV>();
		if (Options.very_verbose)
			System.out.println("Next  |  Processed  |  ProcessedL ProcessedR |cntL");

		Next.addAll(Q1);
		
		if(!Options.testInfo){
			for(NewMetagraph g:Next){
				MetagraphBV left=new MetagraphBV(
						getL(g.getLeft(),system.getInitialState().id,false), 
						getL(g.getRight(),spec.getInitialState().id,true), g.rpstring);
				MetagraphBV right=new MetagraphBV(getR(g.getLeft(),true), getR(g.getRight(),false), g.rpstring);
				
				Iterator<MetagraphBV> ProcessedL_it = ProcessedL.iterator();
				while (ProcessedL_it.hasNext()) {
					MetagraphBV hl = ProcessedL_it.next();
					if (!double_graph_test(hl, right)) {
						processed = Processed.size();
	//						forensics(Processed);
						this.counterexample_prefix = hl.rpstring;
						this.counterexample_loop = right.rpstring;
						return false;
					}
				}
				Iterator<MetagraphBV> ProcessedR_it = ProcessedR.iterator();
				while (ProcessedR_it.hasNext()) {
					MetagraphBV hr = ProcessedR_it.next();
					if (!double_graph_test(left, hr)) {
						processed = Processed.size();
	//						forensics(Processed);
						this.counterexample_prefix = left.rpstring;
						this.counterexample_loop = hr.rpstring;
						return false;
					}
				}
				ProcessedL.add(left);
				ProcessedR.add(right);
			}
		}				
		
		
		mggen += Q1.size();
		if (Options.very_verbose)
			System.out.println(Next.size() + "  |  " + Processed.size()
					+ "  |  " + ProcessedL.size() + "  " + ProcessedR.size()+" | "+cntL);

		while (!Next.isEmpty() && (!Options.C1 || cntL != 0)) {
//checkLLabel(Next, Processed, null, null,null, cntL, 0);

		    if (stop)
				break;

		    if(Options.globalstop) break; // Stop trying. Other thread has proved inclusion.
		    
		    // Give up if number of metagraphs greater than limit. Limit==0 means no limit.
		    if(limit !=0 && mggen >= limit){
			timeout=true;
			break;
		    }

			debug("", 100);
			debug("Begin while loop", 100);
			debug("Processed:" + Processed, 100);
			debug("Next:" + Next, 100);
			Iterator<NewMetagraph> Processed_it;
			NewMetagraph g;
			if (Options.DFS) {
				g = Next.getLast();
			}else if (Options.SFS){ // Smallest graph first
				g = Next.getFirst();
				int findsmall = 0;
				int minsize = g.getRight().size();
				while (findsmall < Next.size()) {
					if (Next.get(findsmall).getRight().size() < minsize) {
						g = Next.get(findsmall);
						minsize = g.getRight().size();
					}
					findsmall++;
				}
			}else{
				g = Next.getFirst(); // Default BFS
			}

			debug("Pick [" + g.rpstring + "] " + g + "from Next", 100);
			if(Options.testInfo){
				MetagraphBV gl=new MetagraphBV(
						getL(g.getLeft(),system.getInitialState().id,false), 
						getL(g.getRight(),spec.getInitialState().id,true), g.rpstring);
				MetagraphBV gr=new MetagraphBV(getR(g.getLeft(),true), getR(g.getRight(),false), g.rpstring);
				debug("Add "+gl+"to ProcessedL",100);
				debug("Add "+gr+"to ProcessedR",100);
				
				
				Iterator<MetagraphBV> ProcessedL_it=ProcessedL.iterator();
				while(ProcessedL_it.hasNext()){
					MetagraphBV hl=ProcessedL_it.next();
					if(!double_graph_test(hl, gr)){
						this.counterexample_prefix = hl.rpstring;
						this.counterexample_loop = gr.rpstring;
						return false;
					}
				}
				Iterator<MetagraphBV> ProcessedR_it=ProcessedR.iterator();
				while(ProcessedR_it.hasNext()){
					MetagraphBV hr=ProcessedR_it.next();
					if(!double_graph_test(gl, hr)){
					    this.counterexample_prefix = gl.rpstring;
					    this.counterexample_loop = hr.rpstring;
					    return false;
					}
				}
				
				ProcessedL.add(gl);
				ProcessedR.add(gr);

			}
			Next.remove(g);
			Processed.add(g);
			if (Options.very_verbose)
				System.out.println(Next.size() + "  |  " + Processed.size()
						+ "  |  " + ProcessedL.size() + "  " + ProcessedR.size()+" | "+cntL);
//checkLLabel(Next, Processed, null, null,null, cntL, 1);

			Graph ori_L = new Graph();
			if (Options.C1) {
				Iterator<Integer> leftSt_it = g.getLeft().leftStateIt();
				while (leftSt_it.hasNext()) {
					Iterator<Arc> g_it = g.getLeft().iterator(
							leftSt_it.next());
					while (g_it.hasNext()) {
						Arc left = g_it.next();
						if (left.L) {
							ori_L.add(left);
							left.L = false;
							cntL--;
						}
					}
				}
				debug("Move" + g
						+ "from Next to Processed with L label removed", 100);
//checkLLabel(Next, Processed, null, null, null, cntL, 2);
			} else {
				debug("Move" + g + "from Next to Processed", 100);
			}

			Q1_it = Q1.iterator();
			while (Q1_it.hasNext()) {
				NewMetagraph h = Q1_it.next();
//checkLLabel(Next, Processed, null, null, null, cntL, 21);
				NewMetagraph f = compose(g, h, ori_L);

			    if(Options.rd&&Options.EB){
			    	if(f!=null&& f.getRight().size()==0&&f.getLeft().size()>0){
				    this.counterexample_prefix = "Can't tell you the counterexample. Run without option -eb to get one, i.e., -fastc instead of -fast";
				    this.counterexample_loop = "";
			    		return false;
			    	}
			    }
				
				//checkLLabel(Next, Processed, null, null, f, cntL, 22);
				if (f == null)
					continue;
				f = min_plus(f);

			    if(Options.rd&&Options.EB){
		    		if(!f.getRight().containsLeftState(spec.getInitialState().id)&&
		    			f.getLeft().containsLeftState(system.getInitialState().id)){
				        this.counterexample_prefix = "Can't tell you the counterexample. Run without option -eb to get one, i.e., -fastc instead of -fast";
					this.counterexample_loop = "";
	    				return false;
		    		}
		    	}
				
				
				debug("Produce f:[" + f.rpstring + "]=[" + g.rpstring + "];["
						+ h.rpstring + "]), " + f, 100);
//checkLLabel(Next, Processed, null, null, f, cntL, 23);

				ArrayList<NewMetagraph> toRemove = new ArrayList<NewMetagraph>();
				ArrayList<NewMetagraph> toAdd = new ArrayList<NewMetagraph>();
				Iterator<NewMetagraph> Next_it = Next.iterator();
				while (Next_it.hasNext()) {
					NewMetagraph p = Next_it.next();
					cleanLayered(f, p, (short) 1);
					if (f.getLeft().size() == 0)
						break;
//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 3);

					Graph left = new Graph();
					left.addAll(p.getLeft());
					Graph right = new Graph();
					right.addAll(p.getRight());
					NewMetagraph p_new = new NewMetagraph(left, right,
							p.rpstring);
					boolean changed=cleanLayered(p_new, f, (short) 3);
//					if(changed!=(p_new.compareTo(p) != 0)){
//						System.exit(0);
//					}
//					if (p_new.compareTo(p) != 0) {
					if (changed) {
						toRemove.add(p);
						if (p_new.getLeft().size() > 0)
							toAdd.add(p_new);
					}
//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 4);
					
				}
				if (toAdd.size() > 0) {
					Next.addAll(toAdd);
					if (Options.very_verbose)
						System.out.println(Next.size() + "  |  " + Processed.size()
								+ "  |  " + ProcessedL.size() + "  " + ProcessedR.size()+" | "+cntL);
					toAdd.clear();
				}
				if (f.getLeft().size() == 0)
					continue;
				Processed_it = Processed.iterator();
//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 48);
				while (Processed_it.hasNext()) {
					NewMetagraph p = Processed_it.next();
//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 49);
					cleanLayered(f, p, (short) 2);
//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 5);
					if (f.getLeft().size() == 0)
						break;

					Graph left = new Graph();
					left.addAll(p.getLeft());
					Graph right = new Graph();
					right.addAll(p.getRight());
					NewMetagraph p_new = new NewMetagraph(left, right,
							p.rpstring);
					boolean changed=cleanLayered(p_new, f, (short) 3);
//					if (p_new.compareTo(p) != 0) {
					if (changed) {
						toRemove.add(p);
						if (p_new.getLeft().size() > 0)
							toAdd.add(p_new);
					}
//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 6);
					
				}
				if (f.getLeft().size() == 0)
					continue;

				Processed.removeAll(toRemove);
				Next.removeAll(toRemove);
				Processed.addAll(toAdd);
				
				MetagraphBV left = new MetagraphBV(getL(f.getLeft(),system.getInitialState().id, false), 
								   getL(f.getRight(), spec.getInitialState().id, true), 
								   f.rpstring);
				MetagraphBV right = new MetagraphBV(getR(f.getLeft(), true), getR(f.getRight(), false), f.rpstring);

				if(!Options.testInfo){
	
					Iterator<MetagraphBV> ProcessedL_it = ProcessedL.iterator();
					while (ProcessedL_it.hasNext()) {
						MetagraphBV hl = ProcessedL_it.next();
						if (!double_graph_test(hl, right)) {
						        this.counterexample_prefix = hl.rpstring;
							this.counterexample_loop = right.rpstring;
							processed = Processed.size();
							//forensics(Processed);
							return false;
						}
					}
					Iterator<MetagraphBV> ProcessedR_it = ProcessedR.iterator();
					while (ProcessedR_it.hasNext()) {
						MetagraphBV hr = ProcessedR_it.next();
						if (!double_graph_test(left, hr)) {
						        this.counterexample_prefix = left.rpstring;
							this.counterexample_loop = hr.rpstring;
							processed = Processed.size();
							//forensics(Processed);
							return false;
						}
					}
					ProcessedL.add(left);
					ProcessedR.add(right);
				}				
				debug("Add [" + f.rpstring + "] " + f + " to Next", 100);
				debug("Generate left bit vector" + left, 100);
				debug("Generate right bit vector" + right, 100);
				if (!double_graph_test(left, right)) {
				        this.counterexample_prefix = left.rpstring;
					this.counterexample_loop = right.rpstring;
					processed = Processed.size();
//					forensics(Processed);
					return false;
				}

//checkLLabel(Next, Processed, toRemove, toAdd, f, cntL, 7);
				
				
				
//checkLLabel(Next, Processed, null,null,f, cntL, 8);
				if (Options.very_verbose)
					System.out.println(Next.size() + "  |  " + Processed.size()
							+ "  |  " + ProcessedL.size() + "  " + ProcessedR.size()+" | "+cntL);

				mggen++;
				// Next_it=Next.iterator();
				// while(Next_it.hasNext()){
				// Pair<Graph, Graph> cur=Next_it.next();
				// if(cur.getRight().toString().compareToIgnoreCase(f.getRight().toString())==0){
				// merged=true;
				// cur.getLeft().addAll(f.getLeft());
				// break;
				// }
				// }
				// if(!merged)

				Next.add(f);
				if (Options.very_verbose)
					System.out.println(Next.size() + "  |  " + Processed.size()
							+ "  |  " + ProcessedL.size() + "  " + ProcessedR.size()+" | "+cntL);
			}
		}
		processed = Processed.size();
		    // forensics(Processed);
		return true;
	}

	private void checkLLabel(LinkedList<NewMetagraph> next,
			LinkedList<NewMetagraph> processed2, ArrayList<NewMetagraph> toRemove, ArrayList<NewMetagraph> toAdd, NewMetagraph f, int cntL2, int loc) {
		if(!Options.C1)
			return;
		int cnt=0;
		if(toRemove!=null)
		for(NewMetagraph g:toRemove){
			for(Arc a:g.getLeft()){
				if(a.L){
					cnt--;
				}
			}
		}
		if(toAdd!=null)
		for(NewMetagraph g:toAdd){
			for(Arc a:g.getLeft()){
				if(a.L){
					cnt++;
				}
			}
		}

		
		for(NewMetagraph g:next){
			for(Arc a:g.getLeft()){
				if(a.L){
					cnt++;
				}
			}
		}
		for(NewMetagraph g:processed2){
			for(Arc a:g.getLeft()){
				if(a.L){
					cnt++;
				}
			}
		}
		if(f!=null)
		for(Arc a:f.getLeft()){
			if(a.L){
				cnt++;
			}
		}

		
		if (! (cnt==cntL2)){
			System.out.println(toRemove);
			System.out.println(toAdd);
			System.out.println(next);
			System.out.println(processed2);
			System.out.println(f);
			System.out.println("L label counter error: real="+cnt+"cnt="+cntL2+" @"+loc);
			System.exit(0);
		}else{
//			if(loc==49){
//				System.out.println(toRemove);
//				System.out.println(toAdd);
//				System.out.println(next);
//				System.out.println(processed2);
//				System.out.println(f);
//			}
			System.out.println("L label counter : real="+cnt+"cnt="+cntL2+" @"+loc);
		}
	}

    private int find_rightuseless(NewMetagraph p)
    {
	int useless_counter=0;
	boolean has_larger=false;
	
	Iterator<Integer> leftSt_it=p.getLeft().leftStateIt();
	while(leftSt_it.hasNext()){
	    Iterator<Arc> A_it=p.getLeft().iterator(leftSt_it.next());
	    while(A_it.hasNext()){
		Arc l=A_it.next();
		has_larger=false;
		Iterator<FAState> bwLgSts_it=brelM.get(new FAState(l.getFrom(),system)).iterator();
		while(bwLgSts_it.hasNext()){
		    FAState bwLgSt=bwLgSts_it.next();
		    if(bwLgSt.getowner()!=spec)	continue;
		    Iterator<Arc> B_it=p.getRight().iterator(bwLgSt.getID());
		    while(B_it.hasNext()){
			Arc r=B_it.next();
			if(true
			   //!l.getLabel()||r.getLabel()   This condition is not actually needed.
                          ){
			    if(frelM.get(new FAState(l.getTo(),system)).contains(new FAState(r.getTo(),spec)))
				{ has_larger=true; break; }
			}
		    }
		    if(has_larger) break;
		}
		if(has_larger) ++useless_counter;
	    }
	}
	return useless_counter;
    }

    private void forensics(LinkedList<NewMetagraph> processed2)
    {
// Forensics on Processed.
		Iterator<NewMetagraph> Processed_it=processed2.iterator();
		while(Processed_it.hasNext()){
			NewMetagraph p=Processed_it.next();
			System.out.println("Useless: "+find_rightuseless(p)+"of "+p.getLeft().size()+", B: "+p.getRight().size());
		}
    }


}

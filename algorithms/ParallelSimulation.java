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
import java.lang.Math;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.*;

import automata.FAState;
import automata.FiniteAutomaton;
import comparator.StateComparator;
import comparator.StatePairComparator;
import datastructure.HashSet;
import datastructure.Pair;
import datastructure.State_Label;


/**
 * 
 * @author Richard Mayr
 * This package does the same as Simulation.java, but using Java 7 fork-join concurrency
 */
public class ParallelSimulation{

		private static final int num_proc = Runtime.getRuntime().availableProcessors();
		private static final ForkJoinPool forkJoinPool = new ForkJoinPool(num_proc);
	/**
	 * Compute delayed (forward) simulation relation on/between two Buchi automata
	 * @param omega1, omega2: two Buchi automata
	 *
	 * @return maximal delayed simulation relation
	 */


	// Aux. code for for delayed simulation
        /* Now obsolete
	private boolean trapped(int s, int q, int a, int[][][] post, int[][] post_len, boolean[][] X)
        {
	    if(post_len[a][q]>0){
		    for(int r=0; r<post_len[a][q]; r++)
			if(!X[s][post[a][q][r]]) return false;
	    }
	    return true;
	}
	*/

       private boolean CPre(int p, int q, int n_symbols, int[][][] post, int[][] post_len, boolean[][] X)
        {
	    boolean trapped=false;
	    for(int a=0; a<n_symbols; a++)
		if(post_len[a][p]>0){
		    for(int r=0; r<post_len[a][p]; r++){ 
			trapped=true;
			if(post_len[a][q]>0) for(int t=0; t<post_len[a][q]; t++)
						 if(!X[post[a][p][r]][post[a][q][t]]) { trapped=false; break; }
			if(trapped) return true;
		    }
		}
	    return false;
	}


    class par_get_avoid extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[][] avoid;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	
	par_get_avoid(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.avoid=avoid;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	}

	protected Integer compute(){
	    if ((p2-p1 <= Math.max(50,n_states/16)) || (q2-q1 <= Math.max(50,n_states/16))) {
		return single_get_avoid(p1,p2,q1,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
	    }
	    else{
		par_get_avoid t1 = new par_get_avoid(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		par_get_avoid t2 = new par_get_avoid(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		par_get_avoid t3 = new par_get_avoid(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		par_get_avoid t4 = new par_get_avoid(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }


private void get_avoid(boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W)
    {
	for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++)
		avoid[p][q]=true;
	boolean changed=true;
	while(changed){
	    changed=(forkJoinPool.invoke(new par_get_avoid(0,n_states,0,n_states,avoid,isFinal,n_states,n_symbols,post,post_len,W)) >0);
	}
    }


    private int single_get_avoid(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W)
        {
	    //System.out.println("Computing getavoid.");
	
	    // System.out.println("Invoking single: "+p1+","+p2+","+q1+","+q2);
	    boolean changed=false;
		    for(int p=p1; p<p2; p++)
			for(int q=q1; q<q2; q++){
			    if(W[p][q] || !avoid[p][q]) continue; // If W then it stays true. If avoid false then stay false
			    if(isFinal[q]) { avoid[p][q]=false; changed=true; continue; }
			    if(!CPre(p,q,n_symbols,post,post_len,avoid)) { avoid[p][q]=false; changed=true; }
			}
		    if(changed) return(1); else return(0);
	}

	    
	public Set<Pair<FAState,FAState>> DelayedSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		boolean[][] W = new boolean[n_states][n_states];

		FAState[] states = all_states.toArray(new FAState[0]);
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		//state[post[s][q][r]] is in post_s(q) for 0<=r<adj_len[s][q]
		//state[pre[s][q][r]] is in pre_s(q) for 0<=r<adj_len[s][q]
		// System.out.println("Delayed sim: Getting post");
		for(int s=0;s<n_symbols;s++)
		{
		    // System.out.println("Symbol "+s+" of "+n_symbols);
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				//System.out.println("Delayed sim: Getting post: Iterating p: "+p+" of "+n_states+" s is "+s+" of "+n_symbols);
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						//if p --a--> q, then p is in pre_a(q), q is in post_a(p) 
						// pre[s][q][pre_len[s][q]++] = p;
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		// Initialize result. This will grow by least fixpoint iteration.
		boolean[][] avoid = new boolean[n_states][n_states];
				   
		boolean changed=true;
		while(changed){
		    // System.out.println("Delayed sim. Outer iteration.");
		    // changed=false;
		    get_avoid(avoid,isFinal,n_states,n_symbols,post,post_len,W);
		    changed=refine_W(avoid,isFinal,n_states,n_symbols,post,post_len,W);
		    /*
		    for(int p=0; p<n_states; p++)
			for(int q=0; q<n_states; q++){
			    if(W[p][q]) continue;
			    if(isFinal[p] && avoid[p][q]) { W[p][q]=true; changed=true; continue; }
			    if(CPre(p,q,n_symbols,post,post_len,W)) { W[p][q]=true; changed=true; }
			}
		    */
		}
		}
		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(!W[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean refine_W(boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W)
    {
	boolean changed=(forkJoinPool.invoke(new par_refine_W(0,n_states,0,n_states,avoid,isFinal,n_states,n_symbols,post,post_len,W)) >0);
	return changed;
    }



    class par_refine_W extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[][] avoid;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	
	par_refine_W(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.avoid=avoid;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	}

	protected Integer compute(){
	    if ((p2-p1 <= Math.max(50,n_states/16)) || (q2-q1 <= Math.max(50,n_states/16))) {
		return single_refine_W(p1,p2,q1,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
	    }
	    else{
		par_refine_W t1 = new par_refine_W(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		par_refine_W t2 = new par_refine_W(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		par_refine_W t3 = new par_refine_W(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		par_refine_W t4 = new par_refine_W(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }


   private int single_refine_W(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W)
        {
	    boolean changed=false;
	    for(int p=p1; p<p2; p++)
		for(int q=q1; q<q2; q++){
			    if(W[p][q]) continue;
			    if(isFinal[p] && avoid[p][q]) { W[p][q]=true; changed=true; continue; }
			    if(CPre(p,q,n_symbols,post,post_len,W)) { W[p][q]=true; changed=true; }
			}
	    if(changed) return(1); else return(0);
	}



        static class delayed_PrerefThread extends Thread {
	    int n_states;
	    int n_symbols;
	    int[][][] post;
	    int[][] post_len;
	    boolean[][] W;
	    int depth;
	    boolean[] stop;
	    int[] removed;

	    delayed_PrerefThread(int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int depth, boolean[] stop, int[] removed){
             this.n_states = n_states;
	     this.n_symbols = n_symbols;
	     this.post = post;
	     this.post_len = post_len;
	     this.W = W;
	     this.depth = depth;
	     this.stop = stop;
	     this.removed = removed;
	    }

	    public void run() {
    ArrayList<ArrayList<Set<int[]>>> cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> fulldo = new ArrayList<Set<int[]>>(depth);

    cando.add(0,new ArrayList<Set<int[]>>(n_states));
    // cando.get(0).ensureCapacity(n_states);
    for(int p=0; p<n_states; p++) cando.get(0).add(p,new HashSet<int[]>());
    fulldo.add(0,new HashSet<int[]>());
    
    for(int s=0; s<n_symbols; s++){
	int[] seq = new int[1];
	seq[0]=s;
	boolean flag=false;
	// fulldo.get(0).add(seq);
	for(int p=0; p<n_states; p++){
	    if(post_len[s][p] >0){
		(cando.get(0).get(p)).add(seq);
		if(!flag) { fulldo.get(0).add(seq); flag=true; }
	    }
	}
    }


    int res=0;
    for(int d=1; d<depth; d++){
	cando.add(d,new ArrayList<Set<int[]>>(n_states));
	for(int p=0; p<n_states; p++) cando.get(d).add(p, new HashSet<int[]>());
	fulldo.add(d, new HashSet<int[]>());
	Iterator<int[]> it = fulldo.get(d-1).iterator();
	while(it.hasNext()){
	    int[] oldseq = it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){
		    if(stop[0]) return;
		    for(int r=0; r<post_len[s][p]; r++)
			if(cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    cando.get(d).get(p).add(seq);
			    if(!flag) { fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(stop[0]) return;
		if(W[p][q]) continue; // true stays true for delayed sim.
		if(!cando.get(d).get(q).containsAll(cando.get(d).get(p))){
		    // count the number of changes since last reset
		    ++removed[0];
		    W[p][q]=true; // Spoiler wins. He can do a sequence that Duplicator cannot do.
		    res++;
		}
	    }
	// System.out.println("Delayed sim prerefine. Depth "+d+" : Removed so far: "+res);
    }
	    }
	}


	/**
	 * Like unref_BLADelayedSimRelNBW, except for the prerefine in paraellel. Note that W is winning for Spoiler here, so it grows (unlike for direct sim).
	 * Compute the transitive closure of bounded lookahead delayed forward simulation relation on/between two Buchi automata
	 * This is an underapproximation of n-pebble delayed forward simulation, and thus good for quotienting Buchi automata
	 * @param omega1, omega2: two Buchi automata. la: lookahead must be >=1.
	 *
	 * @return An underapproximation of n-pebble delayed forward simulation
	 */

    public Set<Pair<FAState,FAState>> BLADelayedSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, int la){
	if(la<=2) return classic_BLADelayedSimRelNBW(omega1, omega2, la);
	else return h3_BLADelayedSimRelNBW(omega1, omega2, la);
    }


public Set<Pair<FAState,FAState>> classic_BLADelayedSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, int la) 
	{
	    // System.out.println("BLADelayedSimRelNBW: Using "+num_proc+" worker threads.");
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		boolean[][] W = new boolean[n_states][n_states];

		FAState[] states = all_states.toArray(new FAState[0]);
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				//System.out.println("Delayed sim: Getting post: Iterating p: "+p+" of "+n_states+" s is "+s+" of "+n_symbols);
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}
		
		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		// Start new thread for removing pairs: one can do a sequence of symbols that the other can't 
		// Only up-to depth 13, since otherwise it uses too much memory.
		// stop[0] is used as a flag to tell the thread to stop earlier, if needed.
		boolean[] stop = new boolean[1];
		stop[0]=false;
		int[] removed = new int[1];
		removed[0]=0;
		delayed_PrerefThread preref = new delayed_PrerefThread(n_states,n_symbols,post,post_len,W,parallel_depth_pre_refine(la, n_symbols),stop,removed);
		preref.start();

		boolean[][] avoid = new boolean[n_states][n_states];
		boolean changed=true;
		while(changed){
		    delayed_bla_get_avoid(avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		    changed=delayed_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		    if(removed[0] >0) changed=true;
		    removed[0]=0;
		}
		stop[0]=true;
		try{
		    preref.join();
		}
		catch (InterruptedException e) {};

		}
		// Invert to get duplicator winning states
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) W[p][q]=!W[p][q];

		// Compute transitive closure
		close_transitive(W,n_states);
		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}



	/**
	 * Compute the transitive closure of bounded lookahead delayed forward simulation relation on/between two Buchi automata
	 * This is an underapproximation of n-pebble delayed forward simulation, and thus good for quotienting Buchi automata
	 * @param omega1, omega2: two Buchi automata. la: lookahead must be >=1.
	 *
	 * @return An underapproximation of n-pebble delayed forward simulation
	 */

public Set<Pair<FAState,FAState>> unref_BLADelayedSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, int la) 
	{
	    // System.out.println("Using "+num_proc+" worker threads.");
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		boolean[][] W = new boolean[n_states][n_states];

		FAState[] states = all_states.toArray(new FAState[0]);
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				//System.out.println("Delayed sim: Getting post: Iterating p: "+p+" of "+n_states+" s is "+s+" of "+n_symbols);
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}
		
		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		boolean[][] avoid = new boolean[n_states][n_states];
				    
		boolean changed=true;

		while(changed){
		    delayed_bla_get_avoid(avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		    changed=delayed_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		}

		}
		// Invert to get duplicator winning states
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) W[p][q]=!W[p][q];

		// Compute transitive closure
		close_transitive(W,n_states);
		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}

private boolean delayed_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la)
    {
	boolean changed=(forkJoinPool.invoke(new par_delayed_BLA_refine(0,n_states,0,n_states,isFinal,n_states,n_symbols,post,post_len,W,avoid,la)) >0);
	return changed;
    }


    class par_delayed_BLA_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[][] avoid;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	
	par_delayed_BLA_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.avoid=avoid;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(50,n_states/8))) || (q2-q1 <= (Math.max(50,n_states/8)))) {
		return single_delayed_BLA_refine(p1,p2,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
	    }
	    else{
		par_delayed_BLA_refine t1 = new par_delayed_BLA_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		par_delayed_BLA_refine t2 = new par_delayed_BLA_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		par_delayed_BLA_refine t3 = new par_delayed_BLA_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		par_delayed_BLA_refine t4 = new par_delayed_BLA_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }


private int single_delayed_BLA_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		if(W[p][q]) continue; // true remains true; spoiler winning
		attack[0]=p;
		if(delayed_BLA_attack(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,0)) { W[p][q]=true; changed=true; }
	    }
	if(changed) return(1); else return(0);
    }

private boolean delayed_BLA_attack(int p, int q, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!delayed_BLA_defense(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,0,false)); 
    
    if (depth > 0){
	if(delayed_BLA_defense(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,(depth/2),attack,0,false)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!delayed_BLA_defense(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,(depth/2),attack,0,false));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(delayed_BLA_attack(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private boolean delayed_BLA_defense(int p, int q, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, int[] attack, int depth, boolean obligation)
{
    boolean ob=obligation;
    if(isFinal[attack[depth]]) ob=true;
    if(isFinal[q]) ob=false;

    boolean res=false;
    if(ob) res=(!avoid[attack[depth]][q]);
    else res=(!W[attack[depth]][q]);
   
    if(depth==2*la) return res;  // end of attack. the chips are down

    if((depth >0) && res) return true;  // successful defence against prefix of attack

    int s=attack[depth+1];
    if(post_len[s][q]==0) return(false); // duplicator can't make a move
    for(int r=0; r<post_len[s][q]; r++){
	if(delayed_BLA_defense(p,post[s][q][r],isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2,ob)) return true;
    }
    return false;
}

private void delayed_bla_get_avoid(boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
        {
	    //System.out.println("Computing getavoid.");
	    // Starting with true, except where duplicator accepts Will be refined down.
	   for(int p=0; p<n_states; p++)
	       for(int q=0; q<n_states; q++){
		   if(isFinal[q] && !W[p][q]) avoid[p][q]=false; else avoid[p][q]=true;
	       }
				    
		boolean changed=true;
		while(changed){
		    changed=(forkJoinPool.invoke(new par_delayed_bla_get_avoid_refine(0,n_states,0,n_states,avoid,isFinal,n_states,n_symbols,post,post_len,W,la)) >0);
		}
	}


private int single_delayed_bla_get_avoid_refine(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		if(W[p][q] || !avoid[p][q]) continue; // If W then it stays true. If avoid false then stay false
		// (now redundant)  if(isFinal[q]) { avoid[p][q]=false; changed=true; continue; }
		attack[0]=p;
		if(!delayed_BLA_attack_inavoid(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,0)) { avoid[p][q]=false; changed=true; }
	    }
	if(changed) return(1); else return(0);
    }


    class par_delayed_bla_get_avoid_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[][] avoid;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	
	par_delayed_bla_get_avoid_refine(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.avoid=avoid;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(50,n_states/8))) || (q2-q1 <= (Math.max(50,n_states/8)))) {
		return single_delayed_bla_get_avoid_refine(p1,p2,q1,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
	    }
	    else{
		par_delayed_bla_get_avoid_refine t1 = new par_delayed_bla_get_avoid_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		par_delayed_bla_get_avoid_refine t2 = new par_delayed_bla_get_avoid_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		par_delayed_bla_get_avoid_refine t3 = new par_delayed_bla_get_avoid_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		par_delayed_bla_get_avoid_refine t4 = new par_delayed_bla_get_avoid_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }


private boolean delayed_BLA_attack_inavoid(int p, int q, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!delayed_BLA_defense_inavoid(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,0)); 
    
    if (depth > 0){
	if(delayed_BLA_defense_inavoid(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,(depth/2),attack,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!delayed_BLA_defense_inavoid(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,(depth/2),attack,0));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(delayed_BLA_attack_inavoid(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private boolean delayed_BLA_defense_inavoid(int p, int q, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, int[] attack, int depth)
{
    boolean res=(!avoid[attack[depth]][q]);
   
    if(depth==2*la) return res;  // end of attack. the chips are down

    if((depth >0) && res) return true;  // successful defence against nonempty prefix of attack

    int s=attack[depth+1];
    if(post_len[s][q]==0) return(false); // duplicator can't make a move
    for(int r=0; r<post_len[s][q]; r++){
	if(delayed_BLA_defense_inavoid(p,post[s][q][r],isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2)) return true;
    }
    return false;
}

    private int close_transitive(boolean[][] W, int size)
    {
	int result=0;
	for(int r=0; r<size; r++)
	  for(int p=0; p<size; p++)
	      if((p != r) && W[p][r]){
		  for(int q=0; q<size; q++){
		      if(W[p][q]) continue; // true stays true
		      if(W[r][q]) { W[p][q]=true; ++result; }
		  }
	      }
      return result;
    }


    // ----------------------------------------------------------------------------------------------------


/* h3 parallel delayed BLA simulation. The current speed optimized version  */


public Set<Pair<FAState,FAState>> h3_BLADelayedSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, int la) 
	{
	    // System.out.println("BLADelayedSimRelNBW: Using "+num_proc+" worker threads.");
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		boolean[][] W = new boolean[n_states][n_states];

		FAState[] states = all_states.toArray(new FAState[0]);
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				//System.out.println("Delayed sim: Getting post: Iterating p: "+p+" of "+n_states+" s is "+s+" of "+n_symbols);
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}
		
		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		// Start new thread for removing pairs: one can do a sequence of symbols that the other can't 
		// Only up-to depth 13, since otherwise it uses too much memory.
		// stop[0] is used as a flag to tell the thread to stop earlier, if needed.
		boolean[] stop = new boolean[1];
		stop[0]=false;
		int[] removed = new int[1];
		removed[0]=0;
		delayed_PrerefThread preref = new delayed_PrerefThread(n_states,n_symbols,post,post_len,W,parallel_depth_pre_refine(la, n_symbols),stop,removed);
		preref.start();

		boolean[][] avoid = new boolean[n_states][n_states];
		boolean[][] oldavoid = new boolean[n_states][n_states];
		boolean[][] swapavoid;
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) oldavoid[p][q]=false;

		boolean changed=true;
		while(changed){
		    h3_delayed_bla_get_avoid(avoid,isFinal,n_states,n_symbols,post,post_len,W,la,oldavoid);
		    changed = h3_delayed_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		    if(removed[0] >0) changed=true;
		    removed[0]=0;
		    if(changed){  // otherwise the loop will end anyway
			swapavoid=oldavoid;
			oldavoid=avoid;
			avoid=swapavoid;
			//for(int p=0; p<n_states; p++)	
			// for(int q=0; q<n_states; q++) oldavoid[p][q]=avoid[p][q];
		    }
		}
		stop[0]=true;
		try{
		    preref.join();
		}
		catch (InterruptedException e) {};

		}
		// Invert to get duplicator winning states
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) W[p][q]=!W[p][q];

		// Compute transitive closure
		close_transitive(W,n_states);
		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}



private boolean h3_delayed_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la)
    {
	boolean changed=(forkJoinPool.invoke(new h3_par_delayed_BLA_refine(0,n_states,0,n_states,isFinal,n_states,n_symbols,post,post_len,W,avoid,la)) >0);
	return changed;
    }


    class h3_par_delayed_BLA_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[][] avoid;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	
	h3_par_delayed_BLA_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.avoid=avoid;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(50,n_states/8))) || (q2-q1 <= (Math.max(50,n_states/8)))) {
		return h3_single_delayed_BLA_refine(p1,p2,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
	    }
	    else{
		h3_par_delayed_BLA_refine t1 = new h3_par_delayed_BLA_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		h3_par_delayed_BLA_refine t2 = new h3_par_delayed_BLA_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		h3_par_delayed_BLA_refine t3 = new h3_par_delayed_BLA_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		h3_par_delayed_BLA_refine t4 = new h3_par_delayed_BLA_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }


private int h3_single_delayed_BLA_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la)
    {
	int[] attack = new int[2*la+1];
	int[][] poss = new int[la+1][n_states];  
	int[] poss_len = new int[la+1];
	int[][] obposs = new int[la+1][n_states]; // 0 means none, 1 means with obligation, 2 means no obligation
	int[] obposs_len = new int[la+1];
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		if(W[p][q]) continue; // true remains true; spoiler winning
		if(p==q) continue; // will always stay false; attacker does not win here.
		attack[0]=p;
		// Initialize the options of defender, and whether he has the obligation to accept
		if(isFinal[p] && !isFinal[q]){
		    obposs_len[0]=1;
		    obposs[0][0]=q;
		    poss_len[0]=0;
		} else{
		    poss_len[0]=1;
		    poss[0][0]=q;
		    obposs_len[0]=0;
		}
		if(h3_delayed_BLA_attack(isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,0,poss,poss_len,obposs,obposs_len)){
		    W[p][q]=true; changed=true;
		    avoid[p][q]=true;  // Normally avoid includes W. Newly true W propagated to avoid (in anticipation of next round avoid).
		}
	    }
	if(changed) return(1); else return(0);
    }


private void h3_delayed_bla_get_avoid(boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, boolean[][] oldavoid)
        {
	    //System.out.println("Computing getavoid.");
	    // Starting with true, except where duplicator accepts Will be refined down.
	   for(int p=0; p<n_states; p++)
	       for(int q=0; q<n_states; q++){
		   if(isFinal[q] && !W[p][q]) avoid[p][q]=false; else avoid[p][q]=true;
	       }
				    
		boolean changed=true;
		while(changed){
		    changed=(forkJoinPool.invoke(new h3_par_delayed_bla_get_avoid_refine(0,n_states,0,n_states,avoid,isFinal,n_states,n_symbols,post,post_len,W,la, oldavoid)) >0);
		}
	}


private int h3_single_delayed_bla_get_avoid_refine(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, boolean[][] oldavoid)
    {
	int[] attack = new int[2*la+1];
	int[][] poss = new int[la+1][n_states];
	int[] poss_len = new int[la+1];
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		// If W then it stays true. If avoid false then stay false. If oldavoid then avoid stays true
		if(oldavoid[p][q] || W[p][q] || !avoid[p][q]) continue; 
		// (now redundant)  if(isFinal[q]) { avoid[p][q]=false; changed=true; continue; }
		attack[0]=p;
		poss[0][0]=q;
		poss_len[0]=1;
		if(!h3_delayed_BLA_attack_inavoid(n_states,n_symbols,post,post_len,W,avoid,la,attack,0,poss,poss_len)) { avoid[p][q]=false; changed=true; }
	    }
	if(changed) return(1); else return(0);
    }


    class h3_par_delayed_bla_get_avoid_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[][] avoid;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	boolean[][] oldavoid;
	
	h3_par_delayed_bla_get_avoid_refine(int p1, int p2, int q1, int q2, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, boolean[][] oldavoid){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.avoid=avoid;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	    this.oldavoid=oldavoid;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(50,n_states/8))) || (q2-q1 <= (Math.max(50,n_states/8)))) {
		return h3_single_delayed_bla_get_avoid_refine(p1,p2,q1,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la,oldavoid);
	    }
	    else{
		h3_par_delayed_bla_get_avoid_refine t1 = new h3_par_delayed_bla_get_avoid_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la,oldavoid);
		h3_par_delayed_bla_get_avoid_refine t2 = new h3_par_delayed_bla_get_avoid_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la,oldavoid);
		h3_par_delayed_bla_get_avoid_refine t3 = new h3_par_delayed_bla_get_avoid_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la,oldavoid);
		h3_par_delayed_bla_get_avoid_refine t4 = new h3_par_delayed_bla_get_avoid_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,avoid,isFinal,n_states,n_symbols,post,post_len,W,la,oldavoid);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }




private boolean h3_delayed_BLA_attack_inavoid(int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, int[] attack, int depth, int[][] poss, int[] poss_len)
{
    // int[] newposs = new int[n_states];
    // int[] newposs_len = new int[1];
    // interate through all one-step extensions of the attack
    boolean hint=false;
    int z = depth/2;

    for(int s=0;s<n_symbols;s++) if(post_len[s][attack[depth]]>0){
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = h3_delayed_BLA_defense_inavoid(n_states,post,post_len,avoid,attack,depth+2,poss[z],poss_len[z],poss[z+1],poss_len,hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.
		
		hint=true;  // newposs is computed
		if(h3_delayed_BLA_attack_inavoid(n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2,poss,poss_len)) return(true);
	    }
	}
    return false;
}


private int h3_delayed_BLA_defense_inavoid(int n_states, int[][][] post, int[][] post_len, boolean[][] avoid, int[] attack, int depth, int[] poss, int poss_len, int[] newposs, int[] newposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];
    int z = depth/2;

    if(hint){
	// weak=true;       if hint==true then at least one entry in newposs must be true
	for(int i=0; i<newposs_len[z]; i++){
		if(!avoid[attack[depth]][newposs[i]]) return(2);
	    }
	return(1); // weak fail since at least one entry in newposs must be true
    } else{
	if(poss_len*poss_len <= 4*n_states){
	    newposs_len[z]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(!avoid[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    arradz(newposs,newposs_len,z,post[s][poss[i]][r]); weak=true; // only weak fail here
		}
	    }
	} else{
	    boolean[] xposs = new boolean[n_states]; // all initially false
	    newposs_len[z]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(!avoid[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    xposs[post[s][poss[i]][r]]=true; weak=true; // only weak fail here
		}
	    }
	    for(int i=0; i<n_states; i++) if(xposs[i]) newposs[newposs_len[z]++]=i;
	}
    }
    if(weak) return(1); else return(0);
}


private boolean h3_delayed_BLA_attack(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, int[] attack, int depth, int[][] poss, int[] poss_len, int[][] obposs, int[] obposs_len)
{
    // int[] newposs = new int[n_states];
    // int[] newposs_len = new int[1];
    // int[] newobposs = new int[n_states];
    // int[] newobposs_len = new int[1];
    boolean hint=false;
    int z = depth/2;

    for(int s=0;s<n_symbols;s++) if(post_len[s][attack[depth]]>0){
	    // First iterate through accepting successors; search heuristic
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(isFinal[post[s][attack[depth]][r]]) { 
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = h3_delayed_BLA_defense_acc(isFinal,n_states,post,post_len,W,avoid,attack,depth+2,poss[z],poss_len[z],obposs[z],obposs_len[z],poss[z+1],poss_len,obposs[z+1],obposs_len,hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.

		hint=true;  // newposs is computed
		if(h3_delayed_BLA_attack(isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2,poss,poss_len,obposs,obposs_len)) return(true);
	    }

	    // Now iterate through non-accepting successors
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(!isFinal[post[s][attack[depth]][r]]) { 
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = h3_delayed_BLA_defense_nonacc(isFinal,n_states,post,post_len,W,avoid,attack,depth+2,poss[z],poss_len[z],obposs[z],obposs_len[z],poss[z+1],poss_len,obposs[z+1],obposs_len,hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.

		hint=true;  // newposs is computed
		if(h3_delayed_BLA_attack(isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,depth+2,poss,poss_len,obposs,obposs_len)) return(true);
	    }
	}
    return false;
}


private int h3_delayed_BLA_defense_acc(boolean[] isFinal, int n_states, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int[] attack, int depth, int[] poss, int poss_len, int[] obposs, int obposs_len, int[] newposs, int[] newposs_len, int[] newobposs, int[] newobposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];
    int z = depth/2;
    
    // attacker is accepting here

    if(hint){
	// weak=true;  if hint then newposs must contain something
	for(int i=0; i<newposs_len[z]; i++){
	    if(!W[attack[depth]][newposs[i]]) return(2);
	}
	for(int i=0; i<newobposs_len[z]; i++){
	    if(!avoid[attack[depth]][newobposs[i]]) return(2);
	}
	return(1);  // only weak fail since newposs nonempty
    } else{
	if((poss_len+obposs_len)*(poss_len+obposs_len) <= 4*n_states){
	    newposs_len[z]=0;
	    newobposs_len[z]=0; 
	    // attacker is acc, irrelevant whether def. had ob before, has it now anyway
	    // First iterate through poss
	    for(int i=0; i<poss_len; i++){  
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(isFinal[post[s][poss[i]][r]]){
			if(!W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense; new state acc, no obligation, sufficient to be outside W for def. win
			arradz(newposs,newposs_len,z,post[s][poss[i]][r]); weak=true; // only weak fail here; no obligation to acc for def. (just did it)
		    } else{
			if(!avoid[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense; new state nonacc, obligation, needs to be outside avoid to win
			arradz(newobposs,newobposs_len,z,post[s][poss[i]][r]); // only weak fail here; obligation to acc for def.
			weak=true; 
		    }
		}
	    }
	    // Now iterate through obposs
	    for(int i=0; i<obposs_len; i++){  
		for(int r=0; r<post_len[s][obposs[i]]; r++){
		    if(isFinal[post[s][obposs[i]][r]]){
			if(!W[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state acc, no obligation, sufficient to be outside W for def. win
			arradz(newposs,newposs_len,z,post[s][obposs[i]][r]); weak=true; // only weak fail here; no obligation to acc for def. (just did it)
		    } else{
			if(!avoid[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state nonacc, obligation, needs to be outside avoid to win
			arradz(newobposs,newobposs_len,z,post[s][obposs[i]][r]); // only weak fail here; obligation to acc for def.
			weak=true; 
		    }
		}
	    }
	} else{
	    byte xposs[] = new byte[n_states];  // initially all zero
	    // iterate through poss
	    for(int i=0; i<poss_len; i++){  
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(isFinal[post[s][poss[i]][r]]){
			if(!W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense; new state acc, no obligation, sufficient to be outside W for def. win
			xposs[post[s][poss[i]][r]]=2; weak=true; // only weak fail here; no obligation to acc for def. (just did it)
		    } else{
			if(!avoid[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense; new state nonacc, obligation, needs to be outside avoid to win
			if(xposs[post[s][poss[i]][r]]==0) xposs[post[s][poss[i]][r]]=1; // only weak fail here; obligation to acc for def.
			weak=true; 
		    }
		}
	    }
	    // iterate through obposs
	    for(int i=0; i<obposs_len; i++){  
		for(int r=0; r<post_len[s][obposs[i]]; r++){
		    if(isFinal[post[s][obposs[i]][r]]){
			if(!W[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state acc, no obligation, sufficient to be outside W for def. win
			xposs[post[s][obposs[i]][r]]=2; weak=true; // only weak fail here; no obligation to acc for def. (just did it)
		    } else{
			if(!avoid[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state nonacc, obligation, needs to be outside avoid to win
			if(xposs[post[s][obposs[i]][r]]==0) xposs[post[s][obposs[i]][r]]=1; // only weak fail here; obligation to acc for def.
			weak=true; 
		    }
		}
	    }
	    // Collect the results
	    newposs_len[z]=0;
	    newobposs_len[z]=0;
	    for(int i=0; i<n_states; i++){
		if(xposs[i]==2) newposs[newposs_len[z]++]=i;
		else if(xposs[i]==1) newobposs[newobposs_len[z]++]=i;
	    }
	}
    }

    if(weak) return(1); else return(0);
}




private int h3_delayed_BLA_defense_nonacc(boolean[] isFinal, int n_states, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int[] attack, int depth, int[] poss, int poss_len, int[] obposs, int obposs_len, int[] newposs, int[] newposs_len, int[] newobposs, int[] newobposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];
    int z = depth/2;
 
    // attacker not accepting here

   if(hint){
       // weak=true; if hint then newposs must contain something
	for(int i=0; i<newposs_len[z]; i++){
	    if(!W[attack[depth]][newposs[i]]) return(2);
	}
	for(int i=0; i<newobposs_len[z]; i++){
	    if(!avoid[attack[depth]][newobposs[i]]) return(2);
	}
	return(1);
    } else{
       if((poss_len+obposs_len)*(poss_len+obposs_len) <= 4*n_states){
	   newposs_len[z]=0;
	   newobposs_len[z]=0; 
	   // First iterate through poss
	   for(int i=0; i<poss_len; i++){
	       for(int r=0; r<post_len[s][poss[i]]; r++){
		   if(!W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense; no obligation, sufficient to be outside W for def. win
		   arradz(newposs,newposs_len,z,post[s][poss[i]][r]); weak=true; // only weak fail here; no obligation to acc for def.
	       }
	   }
	   // Now iterate through obposs. obposs propagates to obposs, unless accepting (then to poss)
	   for(int i=0; i<obposs_len; i++){
	       for(int r=0; r<post_len[s][obposs[i]]; r++){
		   if(isFinal[post[s][obposs[i]][r]]){
		       if(!W[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state acc, no obligation, sufficient to be outside W for def. win
		       arradz(newposs,newposs_len,z,post[s][obposs[i]][r]); weak=true;
		   } else{
		       if(!avoid[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state nonacc, obligation, needs to be outside avoid to win
		       arrad2z(z,newposs,newposs_len,newobposs,newobposs_len,post[s][obposs[i]][r]); weak=true; // only weak fail here; obligation to acc for def.
		   }
	       }
	   }
       } else{
	   byte xposs[] = new byte[n_states];  // initially all zero
	   // First iterate through poss
	   for(int i=0; i<poss_len; i++){
	       for(int r=0; r<post_len[s][poss[i]]; r++){
		   if(!W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense; no obligation, sufficient to be outside W for def. win
		   xposs[post[s][poss[i]][r]]=2; weak=true; // only weak fail here; no obligation to acc for def.
	       }
	   }
	   // Now iterate through obposs. obposs propagates to obposs, unless accepting (then to poss)
	   for(int i=0; i<obposs_len; i++){
	       for(int r=0; r<post_len[s][obposs[i]]; r++){
		   if(isFinal[post[s][obposs[i]][r]]){
		       if(!W[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state acc, no obligation, sufficient to be outside W for def. win
		       xposs[post[s][obposs[i]][r]]=2; weak=true;
		   } else{
		       if(!avoid[attack[depth]][post[s][obposs[i]][r]]) return(2); // successful defense; new state nonacc, obligation, needs to be outside avoid to win
		       if(xposs[post[s][obposs[i]][r]]==0) xposs[post[s][obposs[i]][r]]=1; weak=true; // only weak fail here; obligation to acc for def.
		   }
	       }
	   }
	   // Collect the results
	   newposs_len[z]=0;
	   newobposs_len[z]=0;
	   for(int i=0; i<n_states; i++){
	       if(xposs[i]==2) newposs[newposs_len[z]++]=i;
	       else if(xposs[i]==1) newobposs[newobposs_len[z]++]=i;
	   }
       }
   }

   if(weak) return(1); else return(0);
}


private void arradz(int[] l, int[] len, int z, int x){
    for(int i=0; i<len[z]; i++) if(l[i]==x) return;
    l[len[z]]=x;
    ++len[z];
    return;
}


private void arrad2z(int z, int[] l0, int[] len0, int[] l, int[] len, int x){
    for(int i=0; i<len0[z]; i++) if(l0[i]==x) return;
    for(int i=0; i<len[z]; i++) if(l[i]==x) return;
    l[len[z]]=x;
    ++len[z];
    return;
}




// ------------------ end of h3 par delayed bla sim -------------------------------------------------------------------








//--------------------------------------------------------------------------------------------


        static class PrerefThread extends Thread {
	    int n_states;
	    int n_symbols;
	    int[][][] post;
	    int[][] post_len;
	    boolean[][] W;
	    int depth;
	    boolean[] stop;

	    PrerefThread(int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int depth, boolean[] stop){
             this.n_states = n_states;
	     this.n_symbols = n_symbols;
	     this.post = post;
	     this.post_len = post_len;
	     this.W = W;
	     this.depth = depth;
	     this.stop = stop;
	    }

	    public void run() {
    ArrayList<ArrayList<Set<int[]>>> cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> fulldo = new ArrayList<Set<int[]>>(depth);

    cando.add(0,new ArrayList<Set<int[]>>(n_states));
    // cando.get(0).ensureCapacity(n_states);
    for(int p=0; p<n_states; p++) cando.get(0).add(p,new HashSet<int[]>());
    fulldo.add(0,new HashSet<int[]>());
    
    for(int s=0; s<n_symbols; s++){
	int[] seq = new int[1];
	seq[0]=s;
	boolean flag=false;
	// fulldo.get(0).add(seq);
	for(int p=0; p<n_states; p++){
	    if(post_len[s][p] >0){
		(cando.get(0).get(p)).add(seq);
		if(!flag) { fulldo.get(0).add(seq); flag=true; }
	    }
	}
    }

    int res=0;
    for(int d=1; d<depth; d++){
	cando.add(d,new ArrayList<Set<int[]>>(n_states));
	for(int p=0; p<n_states; p++) cando.get(d).add(p, new HashSet<int[]>());
	fulldo.add(d, new HashSet<int[]>());
	Iterator<int[]> it = fulldo.get(d-1).iterator();
	while(it.hasNext()){
	    int[] oldseq = it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){
		    // stop if externally told to
		    if(stop[0]) return;
		    for(int r=0; r<post_len[s][p]; r++)
			if(cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    cando.get(d).get(p).add(seq);
			    if(!flag) { fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(stop[0]) return;
		if(!W[p][q]) continue;
		if(!cando.get(d).get(q).containsAll(cando.get(d).get(p))){
		    W[p][q]=false;
		    res++;
		}
	    }
	// System.out.println("Depth "+d+" : Removed so far: "+res);
    }

	    }
	}




        static class acc_PrerefThread extends Thread {
	    int n_states;
	    int n_symbols;
	    int[][][] post;
	    int[][] post_len;
	    boolean[][] W;
	    boolean[] isFinal;
	    int depth;
	    boolean[] stop;
	    int[] removed;

	    acc_PrerefThread(int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[] isFinal, int depth, boolean[] stop, int[] removed){
             this.n_states = n_states;
	     this.n_symbols = n_symbols;
	     this.post = post;
	     this.post_len = post_len;
	     this.W = W;
	     this.isFinal = isFinal;
	     this.depth = depth;
	     this.stop = stop;
	     this.removed = removed;
	    }

	    public void run() {
		    ArrayList<ArrayList<Set<int[]>>> cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> fulldo = new ArrayList<Set<int[]>>(depth);
    ArrayList<ArrayList<Set<int[]>>> acc_cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> acc_fulldo = new ArrayList<Set<int[]>>(depth);

    cando.add(0,new ArrayList<Set<int[]>>(n_states));
    acc_cando.add(0,new ArrayList<Set<int[]>>(n_states));
    // cando.get(0).ensureCapacity(n_states);
    for(int p=0; p<n_states; p++){
	cando.get(0).add(p,new HashSet<int[]>());
	acc_cando.get(0).add(p,new HashSet<int[]>());
    }
    fulldo.add(0,new HashSet<int[]>());
    acc_fulldo.add(0,new HashSet<int[]>());
    
    for(int s=0; s<n_symbols; s++){
	int[] seq = new int[1];
	seq[0]=s;
	boolean flag=false;
	boolean acc_flag=false;
	// fulldo.get(0).add(seq);
	for(int p=0; p<n_states; p++){
	    if(post_len[s][p] >0){
		(cando.get(0).get(p)).add(seq);
		if(!flag) { fulldo.get(0).add(seq); flag=true; }
	    }
	    for(int r=0; r<post_len[s][p]; r++)
		if(isFinal[post[s][p][r]]){
			(acc_cando.get(0).get(p)).add(seq);
			if(!acc_flag) { acc_fulldo.get(0).add(seq); acc_flag=true; }
		    }
	}
    }

    // int res=0;
    for(int d=1; d<depth; d++){
	cando.add(d,new ArrayList<Set<int[]>>(n_states));
	acc_cando.add(d,new ArrayList<Set<int[]>>(n_states));
	for(int p=0; p<n_states; p++){
	    cando.get(d).add(p, new HashSet<int[]>());
	    acc_cando.get(d).add(p, new HashSet<int[]>());
	}
	fulldo.add(d, new HashSet<int[]>());
	acc_fulldo.add(d, new HashSet<int[]>());

	Iterator<int[]> it = fulldo.get(d-1).iterator();
	while(it.hasNext()){
	    int[] oldseq = it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){
		    if(stop[0]) return;
		    for(int r=0; r<post_len[s][p]; r++)
			if(cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    cando.get(d).get(p).add(seq);
			    if(!flag) { fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	Iterator<int[]> acc_it = acc_fulldo.get(d-1).iterator();
	while(acc_it.hasNext()){
	    int[] oldseq = acc_it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){		
		    if(stop[0]) return;
		    for(int r=0; r<post_len[s][p]; r++)
			if(acc_cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    acc_cando.get(d).get(p).add(seq);
			    if(!flag) { acc_fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(stop[0]) return;
		if(!W[p][q]) continue;
		if(!cando.get(d).get(q).containsAll(cando.get(d).get(p))){
		    // Before changing W, record this in removed
		    ++removed[0];
		    W[p][q]=false;
		    // res++;
		    continue;
		}
		if(!acc_cando.get(d).get(q).containsAll(acc_cando.get(d).get(p))){
		    // Before changing W, record this in removed
		    ++removed[0];
		    W[p][q]=false;
		    // res++;
		}
	    }
	// Debug
	// System.out.println("X-Depth "+d+" : Removed so far: "+res);
	
    }
	}
	}



    public Set<Pair<FAState,FAState>> BLASimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];

		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize result. This will shrink by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			if(isFinal[p] && !isFinal[q]) { W[p][q]=false; continue; }
			W[p][q]=true;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=false; // p can do action s, but q cannot
		    }


		BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,la);

		}
		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}



private void BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
		// Start new thread for removing pairs: one can do a sequence of symbols that the other can't 
		// Only up-to depth 13, since otherwise it uses too much memory.
		// stop[0] is used as a flag to tell the thread to stop earlier, if needed.
		boolean[] stop = new boolean[1];
		stop[0]=false;
		// Count the number of pairs that the preref thread has removed since the last sync.
		// Can only terminate when this is zero.
		int[] removed = new int[1];
		removed[0]=0;

		acc_PrerefThread preref = new acc_PrerefThread(n_states,n_symbols,post,post_len,W,isFinal,parallel_depth_pre_refine(la, n_symbols),stop,removed);
		preref.start();

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA sim. Outer iteration.");
		    changed=(forkJoinPool.invoke(new par_BLA_refine(0,n_states,0,n_states,isFinal,n_states,n_symbols,post,post_len,W,la)) >0);
		    if(removed[0]>0) changed=true;
		    removed[0]=0;
		}

		stop[0]=true;
		try{
		    preref.join();
		}
		catch (InterruptedException e) {};
    }



    // ----------------------------------- BLA direct forward ----------------------------------



	/**
	 * Compute the transitive closure of bounded lookahead direct forward simulation on/between two Buchi automata
	 * This is an underapproximation of direct forward trace inclusion.
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A relation that underapproximates direct forward trace inclusion.
	 */

    public Set<Pair<FAState,FAState>> unref_BLASimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];

		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize result. This will shrink by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			if(isFinal[p] && !isFinal[q]) { W[p][q]=false; continue; }
			W[p][q]=true;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=false; // p can do action s, but q cannot
		    }

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA sim. Outer iteration.");
		    changed=unref_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,la);
		}
		}
		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}




private boolean unref_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	boolean changed=(forkJoinPool.invoke(new par_BLA_refine(0,n_states,0,n_states,isFinal,n_states,n_symbols,post,post_len,W,la)) >0);
	return changed;
    }


    class par_BLA_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[] isFinal;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	
	par_BLA_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.isFinal=isFinal;
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(20,n_states/16))) || (q2-q1 <= (Math.max(20,n_states/16)))) {
		return single_BLA_refine(p1,p2,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,la);
	    }
	    else{
		par_BLA_refine t1 = new par_BLA_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,isFinal,n_states,n_symbols,post,post_len,W,la);
		par_BLA_refine t2 = new par_BLA_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,isFinal,n_states,n_symbols,post,post_len,W,la);
		par_BLA_refine t3 = new par_BLA_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,isFinal,n_states,n_symbols,post,post_len,W,la);
		par_BLA_refine t4 = new par_BLA_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,isFinal,n_states,n_symbols,post,post_len,W,la);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }



private int single_BLA_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	int[] poss = new int[n_states];
	int poss_len=0;
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		if(!W[p][q]) continue; // false remains false;
		attack[0]=p;
		poss[0]=q;  // we assume (!isFinal[p] || isFinal[q])) by prev. ref. of W
		poss_len=1;
		if(new4_x_i_BLA_attack(isFinal,n_states,n_symbols,post,post_len,W,la,attack,0,poss,poss_len)) { W[p][q]=false; changed=true; }
	    }
	if(changed) return(1); else return(0);
    }

private boolean new4_x_i_BLA_attack(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth, int[] poss, int poss_len)
{
    int[] newposs = new int[n_states];
    int[] newposs_len = new int[1];

    // interate through all one-step extensions of the attack

    boolean hint=false;
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){

	    // First iterate through accepting successors; search heuristic
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(isFinal[post[s][attack[depth]][r]]) {
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = new4_x_i_BLA_defense_acc(isFinal, n_states, n_symbols, post, post_len, W, attack, depth+2, poss, poss_len, newposs, newposs_len, hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.
		
		hint=true;  // newposs is computed
		if(new4_x_i_BLA_attack(isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2,newposs,newposs_len[0])) return(true);
	    }

	    // Now iterate through non-accepting successors
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(!isFinal[post[s][attack[depth]][r]]) {
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = new4_x_i_BLA_defense_nonacc(isFinal, n_states, n_symbols, post, post_len, W, attack, depth+2, poss, poss_len, newposs, newposs_len, hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.
		
		hint=true;  // newposs is computed
		if(new4_x_i_BLA_attack(isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2,newposs,newposs_len[0])) return(true);
	    }

	}

    return false;
}


private int new4_x_i_BLA_defense_acc(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int[] attack, int depth, int[] poss, int poss_len, int[] newposs, int[] newposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];

    if(hint){
	weak = (newposs_len[0]>0);
	for(int i=0; i<newposs_len[0]; i++){
	    // weak=true;
		if(W[attack[depth]][newposs[i]]) return(2);
	    }
    } else{
	if(poss_len*poss_len <= 4*n_states){
	    // for(int i=0; i<n_states; i++) newposs[i]=false;
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(!isFinal[post[s][poss[i]][r]]) continue;
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    arrad(newposs,newposs_len,post[s][poss[i]][r]); weak=true; // only weak fail here
		}
	    }
	} else{
	    boolean[] xposs = new boolean[n_states]; // all initially false
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(!isFinal[post[s][poss[i]][r]]) continue;
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    xposs[post[s][poss[i]][r]]=true; weak=true; // only weak fail here
		}
	    }
	    for(int i=0; i<n_states; i++) if(xposs[i]) newposs[newposs_len[0]++]=i;
	}
    }
    if(weak) return(1); else return(0);
}


private int new4_x_i_BLA_defense_nonacc(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int[] attack, int depth, int[] poss, int poss_len, int[] newposs, int[] newposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];

    if(hint){
	weak = (newposs_len[0]>0);
	for(int i=0; i<newposs_len[0]; i++){
	    // weak=true;
		if(W[attack[depth]][newposs[i]]) return(2);
	    }
    } else{
	if(poss_len*poss_len <= 4*n_states){
	    // for(int i=0; i<n_states; i++) newposs[i]=false;
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    arrad(newposs,newposs_len,post[s][poss[i]][r]); weak=true; // only weak fail here
		}
	    }
	} else{
	    boolean[] xposs = new boolean[n_states]; // all initially false   
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    xposs[post[s][poss[i]][r]]=true; weak=true; // only weak fail here
		}
	    }
	    for(int i=0; i<n_states; i++) if(xposs[i]) newposs[newposs_len[0]++]=i;
	}
    }
    if(weak) return(1); else return(0);
}


private void arrad(int[] l, int[] len, int x){
    for(int i=0; i<len[0]; i++) if(l[i]==x) return;
    l[len[0]]=x;
    ++len[0];
    return;
}





    // --------------------------------------------------------------------------------------------------




 	/**
	 * Compute the transitive closure of bounded lookahead direct backward simulation on/between two Buchi automata
	 * This is an underapproximation of direct backward trace inclusion (respecting initial and final states).
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A relation that underapproximates direct backward trace inclusion.
	 */

    public Set<Pair<FAState,FAState>> BLABSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];

		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		boolean[] isInit = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
			isInit[i] =states[i].getowner().getInitialState().compareTo(states[i])==0;
		}

		// Actually post is initialized as pre, because all is reversed in bw sim.
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
		    // System.out.println("Symbol "+s+" of "+n_symbols);
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getPre(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getPre(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize result. This will shrink by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			if(isFinal[p] && !isFinal[q]) { W[p][q]=false; continue; }
			if(isInit[p] && !isInit[q]) { W[p][q]=false; continue; }
			W[p][q]=true;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=false; // p can do action s, but q cannot
		    }

		BLAB_refine(isFinal,isInit,n_states,n_symbols,post,post_len,W,la);

		}
		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}



    private void BLAB_refine(boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
		// Start new thread for removing pairs: one can do a sequence of symbols that the other can't 
		// Only up-to depth 13, since otherwise it uses too much memory.
		// stop[0] is used as a flag to tell the thread to stop earlier, if needed.
		boolean[] stop = new boolean[1];
		stop[0]=false;
		// Count the number of pairs that the preref thread has removed since the last sync.
		// Can only terminate when this is zero.
		int[] removed = new int[1];
		removed[0]=0;

		acc_PrerefThread preref = new acc_PrerefThread(n_states,n_symbols,post,post_len,W,isFinal,parallel_depth_pre_refine(la, n_symbols),stop,removed);
		preref.start();

		boolean changed=true;
		while(changed){
		    // System.out.println("BLAB sim. Outer iteration.");
		    changed=(forkJoinPool.invoke(new par_BLAB_refine(0,n_states,0,n_states,isFinal,isInit,n_states,n_symbols,post,post_len,W,la)) >0);
		    if(removed[0]>0) changed=true;
		    removed[0]=0;
		}

		stop[0]=true;
		try{
		    preref.join();
		}
		catch (InterruptedException e) {};
    }



    class par_BLAB_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[] isFinal;
	boolean[] isInit;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	
	par_BLAB_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.isFinal=isFinal;
	    this.isInit=isInit; 
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(20,n_states/16))) || (q2-q1 <= (Math.max(20,n_states/16)))) {
		return single_BLAB_refine(p1,p2,q1,q2,isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
	    }
	    else{
		par_BLAB_refine t1 = new par_BLAB_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
		par_BLAB_refine t2 = new par_BLAB_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
		par_BLAB_refine t3 = new par_BLAB_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
		par_BLAB_refine t4 = new par_BLAB_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }


private int single_BLAB_refine(int p1, int p2, int q1, int q2, boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	int[] poss = new int[n_states];
	int poss_len=0;
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		if(!W[p][q]) continue; // false remains false;
		attack[0]=p;
		poss[0]=q;  // we assume (!isFinal[p] || isFinal[q])) by prev. ref. of W
		poss_len=1;
		//defender starts at q
		if(i_BLAB_attack(isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,0,poss,poss_len)) { W[p][q]=false; changed=true; }
	    }
	if(changed) return(1); else return(0);
    }


private boolean i_BLAB_attack(boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth, int[] poss, int poss_len)
{
    int[] newposs = new int[n_states];
    int[] newposs_len = new int[1];

    // interate through all one-step extensions of the attack

    boolean hint=false;
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){

	    // First iterate through successors that are initial; these should be rare. No caching is done here
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(isInit[post[s][attack[depth]][r]]) {
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = i_BLAB_defense_init(isFinal, isInit, n_states, n_symbols, post, post_len, W, attack, depth+2, poss, poss_len, newposs, newposs_len);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.
		
		if(i_BLAB_attack(isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2,newposs,newposs_len[0])) return(true);
	    }

	    // Now we consider only non-initial successors
	    // First iterate through accepting successors; search heuristic
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(!isInit[post[s][attack[depth]][r]] && isFinal[post[s][attack[depth]][r]]) {
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = i_BLAB_defense_acc(isFinal, n_states, n_symbols, post, post_len, W, attack, depth+2, poss, poss_len, newposs, newposs_len, hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.
		
		hint=true;  // newposs is computed
		if(i_BLAB_attack(isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2,newposs,newposs_len[0])) return(true);
	    }

	    // Now iterate through non-accepting (and non-initial) successors
	    hint=false;
	    for(int r=0; r<post_len[s][attack[depth]]; r++) if(!isInit[post[s][attack[depth]][r]] && !isFinal[post[s][attack[depth]][r]]) {
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		int d = i_BLAB_defense_nonacc(isFinal, n_states, n_symbols, post, post_len, W, attack, depth+2, poss, poss_len, newposs, newposs_len, hint);
		if(d==0) return true; // strong def. fail; successful attack 
		if(d==2) continue; // def. success; this attack failed, but others might still succeed
		// here d==1; weak def. fail, but possibilities computed
		if(depth+2 == 2*la) return true; // tested attack above was of maxdepth; no extension; weak def. fail means fail.
		// Check if last attack state is deadlocked
		int successors=0;
		for(int t=0;t<n_symbols;t++) successors += post_len[t][attack[depth+2]];
		if(successors==0) return true; // No extension of attack possible; weak def. fail means fail.
		
		hint=true;  // newposs is computed
		if(i_BLAB_attack(isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2,newposs,newposs_len[0])) return(true);
	    }

	}

    return false;
}


private int i_BLAB_defense_init(boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int[] attack, int depth, int [] poss, int poss_len, int[] newposs, int[] newposs_len)
{
    boolean weak = false;
    int s=attack[depth-1];

    if(poss_len*poss_len <= 4*n_states){
	newposs_len[0]=0;
	for(int i=0; i<poss_len; i++){
	    for(int r=0; r<post_len[s][poss[i]]; r++){
		if(!isInit[post[s][poss[i]][r]]) continue;  // def. needs to be initial here, since attack[depth] is
		if(isFinal[attack[depth]] && !isFinal[post[s][poss[i]][r]]) continue;  // must repect acceptance condition
		if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		arrad(newposs,newposs_len,post[s][poss[i]][r]); weak=true; // only weak fail here
	    }
	}
    } else{
	boolean[] xposs = new boolean[n_states]; // all initially false
	newposs_len[0]=0;
	for(int i=0; i<poss_len; i++){
	    for(int r=0; r<post_len[s][poss[i]]; r++){
		if(!isInit[post[s][poss[i]][r]]) continue;  // def. needs to be initial here, since attack[depth] is
		if(isFinal[attack[depth]] && !isFinal[post[s][poss[i]][r]]) continue;  // must repect acceptance condition
		if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		xposs[post[s][poss[i]][r]]=true; weak=true; // only weak fail here
	    }
	}
 	for(int i=0; i<n_states; i++) if(xposs[i]) newposs[newposs_len[0]++]=i;
    }    
    if(weak) return(1); else return(0);
}



private int i_BLAB_defense_acc(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int[] attack, int depth, int[] poss, int poss_len, int[] newposs, int[] newposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];

    if(hint){
	weak = (newposs_len[0]>0);
	for(int i=0; i<newposs_len[0]; i++){
		if(W[attack[depth]][newposs[i]]) return(2);
	    }
    } else{
	if(poss_len*poss_len <= 4*n_states){
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(!isFinal[post[s][poss[i]][r]]) continue;
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    arrad(newposs,newposs_len,post[s][poss[i]][r]); weak=true; // only weak fail here
		}
	    }
	} else{
	    boolean[] xposs = new boolean[n_states]; // all initially false
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(!isFinal[post[s][poss[i]][r]]) continue;
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    xposs[post[s][poss[i]][r]]=true; weak=true; // only weak fail here
		}
	    }
	    for(int i=0; i<n_states; i++) if(xposs[i]) newposs[newposs_len[0]++]=i;
	}
    }
    if(weak) return(1); else return(0);
}



private int i_BLAB_defense_nonacc(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int[] attack, int depth, int[] poss, int poss_len, int[] newposs, int[] newposs_len, boolean hint)
{
    boolean weak = false;
    int s=attack[depth-1];

    if(hint){
	weak = (newposs_len[0]>0);
	for(int i=0; i<newposs_len[0]; i++){
		if(W[attack[depth]][newposs[i]]) return(2);
	    }
    } else{
	if(poss_len*poss_len <= 4*n_states){
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    arrad(newposs,newposs_len,post[s][poss[i]][r]); weak=true; // only weak fail here
		}
	    }
	} else{
	    boolean[] xposs = new boolean[n_states]; // all initially false
	    newposs_len[0]=0;
	    for(int i=0; i<poss_len; i++){
		for(int r=0; r<post_len[s][poss[i]]; r++){
		    if(W[attack[depth]][post[s][poss[i]][r]]) return(2); // successful defense
		    xposs[post[s][poss[i]][r]]=true; weak=true; // only weak fail here
		}
	    }
	    for(int i=0; i<n_states; i++) if(xposs[i]) newposs[newposs_len[0]++]=i;
	}
    }
    if(weak) return(1); else return(0);
}





  	/**
	 * Compute the transitive closure of a weaker version of 
	 * bounded lookahead direct backward simulation on/between two Buchi automata:
	 * unlike BLABSimRelNBW it does not respect final states.
	 * This is an underapproximation of backward trace inclusion (respecting only initial states).
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A relation that underapproximates backward trace inclusion.
	 */

    public Set<Pair<FAState,FAState>> weak_BLABSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
			W[p][q]=(!(states[p].getowner().getInitialState().compareTo(states[p])==0)) || (states[q].getowner().getInitialState().compareTo(states[q])==0); // Only initial states matter. Do not respect final states here for weak sim

		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isInit = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isInit[i] =states[i].getowner().getInitialState().compareTo(states[i])==0;
		}
		
		// Actually post is initialized as pre, because all is reversed in bw sim.
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
		    // System.out.println("Symbol "+s+" of "+n_symbols);
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getPre(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getPre(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA B sim. Outer iteration.");
		    changed=weak_BLAB_refine(isInit,n_states,n_symbols,post,post_len,W,la);
		}
		}
		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}



private boolean weak_BLAB_refine(boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	boolean changed=(forkJoinPool.invoke(new par_weak_BLAB_refine(0,n_states,0,n_states,isInit,n_states,n_symbols,post,post_len,W,la)) >0);
	return changed;
    }

    class par_weak_BLAB_refine extends RecursiveTask<Integer> {
	int p1,p2,q1,q2;
	boolean[] isInit;
	int n_states;
	int n_symbols;
	int[][][] post;
	int[][] post_len; 
	boolean[][] W;
	int la;
	
	par_weak_BLAB_refine(int p1, int p2, int q1, int q2, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la){
	    this.p1=p1;
	    this.p2=p2;
	    this.q1=q1;
	    this.q2=q2;
	    this.isInit=isInit; 
	    this.n_states=n_states;
	    this.n_symbols=n_symbols;
	    this.post=post;
	    this.post_len=post_len;
	    this.W=W;
	    this.la=la;
	}

	protected Integer compute(){
	    if ((p2-p1 <= (Math.max(20,n_states/16))) || (q2-q1 <= (Math.max(20,n_states/16)))) {
		return single_weak_BLAB_refine(p1,p2,q1,q2,isInit,n_states,n_symbols,post,post_len,W,la);
	    }
	    else{
		par_weak_BLAB_refine t1 = new par_weak_BLAB_refine(p1,p1+(p2-p1)/2,q1,q1+(q2-q1)/2,isInit,n_states,n_symbols,post,post_len,W,la);
		par_weak_BLAB_refine t2 = new par_weak_BLAB_refine(p1,p1+(p2-p1)/2,q1+(q2-q1)/2,q2,isInit,n_states,n_symbols,post,post_len,W,la);
		par_weak_BLAB_refine t3 = new par_weak_BLAB_refine(p1+(p2-p1)/2,p2,q1,q1+(q2-q1)/2,isInit,n_states,n_symbols,post,post_len,W,la);
		par_weak_BLAB_refine t4 = new par_weak_BLAB_refine(p1+(p2-p1)/2,p2,q1+(q2-q1)/2,q2,isInit,n_states,n_symbols,post,post_len,W,la);
		t2.fork();
		t3.fork();
		t4.fork();
		int r1=t1.compute();
		int r2=t2.join();
		int r3=t3.join();
		int r4=t4.join();
		return(r1+r2+r3+r4);
	    }
	}

    }



private int single_weak_BLAB_refine(int p1, int p2, int q1, int q2, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=p1; p<p2; p++)	
	    for(int q=q1; q<q2; q++){
		if(!W[p][q]) continue; // false remains false;
		attack[0]=p;
		if(weak_BLAB_attack(p,q,isInit,n_states,n_symbols,post,post_len,W,la,attack,0)) { W[p][q]=false; changed=true; }
	    }
	if(changed) return(1); else return(0);
    }


private boolean weak_BLAB_attack(int p, int q, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!weak_BLAB_defense(p,q,isInit,n_states,n_symbols,post,post_len,W,la,attack,0)); 
    
    // if defender can defend against attack so far, then attack fails.
    if (depth > 0){
	if(weak_BLAB_defense(p,q,isInit,n_states,n_symbols,post,post_len,W,(depth/2),attack,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!weak_BLAB_defense(p,q,isInit,n_states,n_symbols,post,post_len,W,(depth/2),attack,0));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(weak_BLAB_attack(p,q,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}


private boolean weak_BLAB_defense(int p, int q, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    // This is removed for weak:  if(isFinal[attack[depth]] && !isFinal[q]) return false;
    if(isInit[attack[depth]] && !isInit[q]) return false;
    if((depth >0) && W[attack[depth]][q]) return true; 
    if(depth==2*la) return(W[attack[depth]][q]);
    int s=attack[depth+1];
    if(post_len[s][q]==0) return(false);
    for(int r=0; r<post_len[s][q]; r++){
	if(weak_BLAB_defense(p,post[s][q][r],isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return true;
    }
    return false;
}



    //------------------------------ Methods that are not yet parallelized -------------------------------

	/**
	 * Compute forward simulation relation of a Buchi automaton
	 * @param omega: a Buchi automaton
	 * @param FSim: the maximal bound of simulation relation
	 * 
	 * @return maximal simulation relation on states of the input automaton with FSim
	 */
	public Set<Pair<FAState,FAState>> FSimRelNBW(FiniteAutomaton omega, Set<Pair<FAState,FAState>> FSim) {
		Set<Pair<FAState,FAState>> nextFSim=new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());		
		boolean changed = true;
		while (changed) {
			changed = false;
			Iterator<Pair<FAState,FAState>> FSim_it=FSim.iterator();
			while(FSim_it.hasNext()){
				Pair<FAState,FAState> pair=FSim_it.next();
				if (NextStateSimulated(FSim, omega, pair.getLeft(), pair.getRight())) {
					nextFSim.add(new Pair<FAState, FAState>(pair.getLeft(),pair.getRight()));
				}else{
					changed=true;
				}
			}

			FSim=nextFSim;
			nextFSim=new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		}
		return FSim;
	}


	public Set<Pair<FAState,FAState>> FastFSimRelNBW(FiniteAutomaton omega, boolean[][] fsim) 
	{
		return FastFSimRelNBW(omega,null,fsim);
	}	
	
	public Set<Pair<FAState,FAState>> FastFSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, boolean[][] fsim) 
	{


		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();
		
		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}
		//implement the HHK algorithm
		int n_states = all_states.size();
		int n_symbols = alphabet.size();
		FAState[] states = all_states.toArray(new FAState[0]);
		ArrayList<String> symbols=new ArrayList<String>(alphabet);
		

		// fsim[u][v]=true iff v in fsim(u) iff v forward-simulates u
		
		int[][][] pre = new int[n_symbols][n_states][];
		int[][][] post = new int[n_symbols][n_states][];
		int[][] pre_len = new int[n_symbols][n_states];
		int[][] post_len = new int[n_symbols][n_states];

		    // Initialize memory of pre/post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				Set<FAState> next = states[p].getNext(a);
				post_len[s][p]=0;
				if (next != null) post[s][p] = new int[states[p].getNext(a).size()];
				Set<FAState> prev = states[p].getPre(a);
				pre_len[s][p]=0;
				if (prev != null) pre[s][p] = new int[states[p].getPre(a).size()];
			    }
		}

		//state[post[s][q][r]] is in post_s(q) for 0<=r<adj_len[s][q]
		//state[pre[s][q][r]] is in pre_s(q) for 0<=r<adj_len[s][q]
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				Set<FAState> next = states[p].getNext(a);
				if (next != null){
				for(int q=0; q<n_states; q++)		
				{
					if(next.contains(states[q]))
					{
						//if p --a--> q, then p is in pre_a(q), q is in post_a(p) 
						pre[s][q][pre_len[s][q]++] = p;
						post[s][p][post_len[s][p]++] = q;
					}
				}
				}
			    }
		}

		int[] todo = new int[n_states*n_symbols];
		int todo_len = 0;
		
		int[][][] remove = new int[n_symbols][n_states][n_states];
		int[][] remove_len = new int[n_symbols][n_states];
		for(int a=0; a<n_symbols; a++)
		{
			for(int p=0; p<n_states; p++)
				if(pre_len[a][p]>0) // p is in a_S
				{	
					Sharpen_S_a:
					for(int q=0; q<n_states; q++)	// {all q} --> S_a 
					{
							if(post_len[a][q]>0)	/// q is in S_a 
							{	
								for(int r=0; r<post_len[a][q]; r++) 
									if(fsim[p][post[a][q][r]]) 	// q is in pre_a(sim(p))
										continue Sharpen_S_a;	// skip q						
								remove[a][p][remove_len[a][p]++] = q;
							}
					}
					if(remove_len[a][p]>0)
						todo[todo_len++] = a*n_states + p;
				}
		}
		int[] swap = new int[n_states];
		int swap_len = 0;
		boolean using_swap = false;
		
		while(todo_len>0)
		{
			todo_len--;
			int v = todo[todo_len] % n_states;
			int a = todo[todo_len] / n_states;
			int len = (using_swap? swap_len : remove_len[a][v]);
			remove_len[a][v] = 0;
			
			for(int j=0; j<pre_len[a][v]; j++)
			{
				int u = pre[a][v][j];
				
				for(int i=0; i<len; i++)			
				{
					int w = (using_swap? swap[i] : remove[a][v][i]);
					if(fsim[u][w]) 
					{
						fsim[u][w] = false;					
						for(int b=0; b<n_symbols; b++)
							if(pre_len[b][u]>0)
							{
								Sharpen_pre_b_w:
								for(int k=0; k<pre_len[b][w]; k++)
								{	
									int ww = pre[b][w][k];
									for(int r=0; r<post_len[b][ww]; r++) 
										if(fsim[u][post[b][ww][r]]) 	// ww is in pre_b(sim(u))
											continue Sharpen_pre_b_w;	// skip ww
									
									if(b==a && u==v && !using_swap)
										swap[swap_len++] = ww;
									else{										
										if(remove_len[b][u]==0)
											todo[todo_len++] = b*n_states + u;
										remove[b][u][remove_len[b][u]++] = ww;
									}
									
								}
							}
					}//End of if(fsim[u][w])
				}				
			}			
			if(swap_len>0)
			{	
				if(!using_swap)
				{	
					todo[todo_len++] = a*n_states + v;	
					using_swap = true; 
				}else{
					swap_len = 0;
					using_swap = false;
				}
			}
			
		}

		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(fsim[p][q]) // q is in sim(p), q simulates p
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
		
	}	

	public Set<Pair<FAState,FAState>> FastBSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, boolean[][] bsim) 
	{


		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();
		
		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}
		//implement the HHK algorithm
		int n_states = all_states.size();
		int n_symbols = alphabet.size();
		FAState[] states = all_states.toArray(new FAState[0]);
		ArrayList<String> symbols=new ArrayList<String>(alphabet);
		

		// fsim[u][v]=true iff v in fsim(u) iff v forward-simulates u
		
		int[][][] pre = new int[n_symbols][n_states][];
		int[][][] post = new int[n_symbols][n_states][];
		int[][] pre_len = new int[n_symbols][n_states];
		int[][] post_len = new int[n_symbols][n_states];
		
		    // Initialize memory of pre/post. Pre/Post reversed because of bw-sim.
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				post_len[s][p]=0;
				pre_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a);
				if (next != null) pre[s][p] = new int[states[p].getNext(a).size()];
				Set<FAState> prev = states[p].getPre(a);
				if (prev != null) post[s][p] = new int[states[p].getPre(a).size()];
			    }
		}

		//state[post[s][q][r]] is in post_s(q) for 0<=r<adj_len[s][q]
		//state[pre[s][q][r]] is in pre_s(q) for 0<=r<adj_len[s][q]
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
				for(int q=0; q<n_states; q++)		
				{
					Set<FAState> prev = states[p].getPre(a); 
					if(prev!=null && prev.contains(states[q]))
					{
						//if p --a--> q, then p is in pre_a(q), q is in post_a(p) (note: it is backward)
						pre[s][q][pre_len[s][q]++] = p;
						post[s][p][post_len[s][p]++] = q;
					}
				}
		}
		int[] todo = new int[n_states*n_symbols];
		int todo_len = 0;
		
		int[][][] remove = new int[n_symbols][n_states][n_states];
		int[][] remove_len = new int[n_symbols][n_states];
		for(int a=0; a<n_symbols; a++)
		{
			for(int p=0; p<n_states; p++)
				if(pre_len[a][p]>0) // p is in a_S
				{	
					Sharpen_S_a:
					for(int q=0; q<n_states; q++)	// {all q} --> S_a 
					{
							if(post_len[a][q]>0)	/// q is in S_a 
							{	
								for(int r=0; r<post_len[a][q]; r++) 
									if(bsim[p][post[a][q][r]]) 	// q is in pre_a(sim(p))
										continue Sharpen_S_a;	// skip q						
								remove[a][p][remove_len[a][p]++] = q;
							}
					}
					if(remove_len[a][p]>0)
						todo[todo_len++] = a*n_states + p;
				}
		}
		int[] swap = new int[n_states];
		int swap_len = 0;
		boolean using_swap = false;
		
		while(todo_len>0)
		{
			todo_len--;
			int v = todo[todo_len] % n_states;
			int a = todo[todo_len] / n_states;
			int len = (using_swap? swap_len : remove_len[a][v]);
			remove_len[a][v] = 0;
			
			for(int j=0; j<pre_len[a][v]; j++)
			{
				int u = pre[a][v][j];
				
				for(int i=0; i<len; i++)			
				{
					int w = (using_swap? swap[i] : remove[a][v][i]);
					if(bsim[u][w]) 
					{
						bsim[u][w] = false;					
						for(int b=0; b<n_symbols; b++)
							if(pre_len[b][u]>0)
							{
								Sharpen_pre_b_w:
								for(int k=0; k<pre_len[b][w]; k++)
								{	
									int ww = pre[b][w][k];
									for(int r=0; r<post_len[b][ww]; r++) 
										if(bsim[u][post[b][ww][r]]) 	// ww is in pre_b(sim(u))
											continue Sharpen_pre_b_w;	// skip ww
									
									if(b==a && u==v && !using_swap)
										swap[swap_len++] = ww;
									else{										
										if(remove_len[b][u]==0)
											todo[todo_len++] = b*n_states + u;
										remove[b][u][remove_len[b][u]++] = ww;
									}
									
								}
							}
					}//End of if(fsim[u][w])
				}				
			}			
			if(swap_len>0)
			{	
				if(!using_swap)
				{	
					todo[todo_len++] = a*n_states + v;	
					using_swap = true; 
				}else{
					swap_len = 0;
					using_swap = false;
				}
			}
			
		}

		Set<Pair<FAState,FAState>> BSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(bsim[p][q]) // q is in sim(p), q simulates p
					BSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return BSim2;
		
	}	
	
	
	
	/**
	 * Compute forward simulation relation of a Buchi automaton using Henzinger, Henzinger, Kopke FOCS 1995
	 * @param omega: a Buchi automaton
	 * @param FSim: maximum simulation relation
	 * 
	 * @return simulation relation on states of the input automaton
	 */
	public Set<Pair<FAState,FAState>> FastFSimRelNBW2(FiniteAutomaton omega, Set<Pair<FAState,FAState>> FSim) {
		TreeMap<State_Label, Set<FAState>> Remove=new TreeMap<State_Label, Set<FAState>>();

		HashMap<String,Integer> symMap=new HashMap<String,Integer>();
		int [][][] counter = new int[omega.states.size()][omega.states.size()][omega.alphabet.size()];
		for(int i=0;i<omega.states.size();i++){
			for(int j=0;j<omega.states.size();j++){
				for(int k=0;k<omega.alphabet.size();k++){
					counter[i][j][k]=0;
				}
			}
		}
		
		Iterator<FAState> state_it=omega.states.iterator();
		while(state_it.hasNext()){
		FAState v=state_it.next();
			Iterator<String> sym_it=omega.getAllTransitionSymbols().iterator();
			int sym_index=0;
			while(sym_it.hasNext()){
				String sym=sym_it.next();
				symMap.put(sym, sym_index);
				sym_index++;
				Set<FAState> allStates=new TreeSet<FAState>();
				allStates.addAll(omega.states);
				Remove.put(new State_Label(v,sym), allStates);
			}
		}
		Iterator<Pair<FAState,FAState>> FSim_it=FSim.iterator();

		while(FSim_it.hasNext()){
			Pair<FAState,FAState> cur=FSim_it.next();
			FAState v=cur.getLeft();
			FAState sim_v=cur.getRight();
			
			Iterator<String> symbol_it=sim_v.preIt();
			while(symbol_it.hasNext()){
				String symbol=symbol_it.next();

				Iterator<FAState> from_it=sim_v.getPre(symbol).iterator();
				while(from_it.hasNext()){
					FAState from=from_it.next();
					if(Remove.get(new State_Label(v,symbol))!=null)
						Remove.get(new State_Label(v,symbol)).remove(from);
					counter[from.id][v.id][symMap.get(symbol)]++;
				}
			}
		}

		while(!Remove.isEmpty()){
			State_Label key=Remove.keySet().iterator().next();
			Set<FAState> remove=Remove.get(key);
			Remove.remove(key);
			FAState v=key.getState();
			String symbol=key.getLabel();
			if(v.getPre(symbol)==null)
				continue;			
			
			Iterator<FAState> pre_it=v.getPre(symbol).iterator();
			while(pre_it.hasNext()){
				FAState u=pre_it.next();
				Iterator<FAState> remove_it=remove.iterator();
				while(remove_it.hasNext()){
					FAState w=remove_it.next();
					if(FSim.contains(new Pair<FAState,FAState>(u,w))){
						FSim.remove(new Pair<FAState,FAState>(u,w));

						Iterator<String> symbol_it=w.preIt();
						while(symbol_it.hasNext()){
							String w_symbol=symbol_it.next();

							Iterator<FAState> w_pre_it=w.getPre(w_symbol).iterator();
							while(w_pre_it.hasNext()){
								FAState w_pre=w_pre_it.next();
								counter[w_pre.id][u.id][symMap.get(w_symbol)]--;
								if(counter[w_pre.id][u.id][symMap.get(w_symbol)]==0){
									if(!Remove.containsKey(new State_Label(u,w_symbol))){
										Set<FAState> emptyStates=new TreeSet<FAState>(new StateComparator());
										Remove.put(new State_Label(u,w_symbol), emptyStates);
									}
									Remove.get(new State_Label(u,w_symbol)).add(w_pre);
								}
							}
						}
					}
				}
			}
		}
		return FSim;
	}

	
	/**
	 * Compute backward simulation relation of a Buchi automaton
	 * @param omega: a Buchi automaton
	 * @param BSim: the maximal bound of simulation relation
	 * 
	 * @return maximal simulation relation on states of the input automaton with BSim
	 */
	public Set<Pair<FAState,FAState>> BSimRelNBW(FiniteAutomaton omega, Set<Pair<FAState,FAState>> BSim) {
		Set<Pair<FAState,FAState>> nextBSim=new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());		
		boolean changed = true;
		while (changed) {
			changed = false;
			Iterator<Pair<FAState,FAState>> BSim_it=BSim.iterator();
			while(BSim_it.hasNext()){
				Pair<FAState,FAState> pair=BSim_it.next();
				if (PreStateSimulated(BSim, omega, pair.getLeft(), pair.getRight())) {
					nextBSim.add(new Pair<FAState, FAState>(pair.getLeft(),pair.getRight()));
				}else{
					changed=true;
				}
			}

			BSim=nextBSim;
			nextBSim=new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		}
		return BSim;
	}
	
	private boolean NextStateSimulated(Set<Pair<FAState, FAState>> sim,
			FiniteAutomaton omega, FAState p, FAState q) {
		Iterator<String> symbol_it=p.nextIt();
		while(symbol_it.hasNext()){
			String a=symbol_it.next();
			Iterator<FAState> p_states=p.getNext(a).iterator();
			if(q.getNext(a)==null)
				return false;
			while(p_states.hasNext()){
				FAState p_next=p_states.next();
				boolean hasSimulatingState = false;
				Iterator<FAState> q_states=q.getNext(a).iterator();
				while(q_states.hasNext()){
					FAState q_next=q_states.next();
					if (sim.contains(new Pair<FAState, FAState>(p_next,q_next))){
						hasSimulatingState = true;
						break;
					}
				}
				if (!hasSimulatingState) {
					return false;
				}
			}
		}
		return true;
	}	

	private boolean PreStateSimulated(Set<Pair<FAState, FAState>> sim,
			FiniteAutomaton omega, FAState p, FAState q) {
		Iterator<String> symbol_it=p.preIt();
		while(symbol_it.hasNext()){
			String a=symbol_it.next();
			Iterator<FAState> p_states=p.getPre(a).iterator();
			if(q.getPre(a)==null)
				return false;
			while(p_states.hasNext()){
				FAState p_pre=p_states.next();
				boolean hasSimulatingState = false;
				Iterator<FAState> q_states=q.getPre(a).iterator();
				while(q_states.hasNext()){
					FAState q_pre=q_states.next();
					if (sim.contains(new Pair<FAState, FAState>(p_pre,q_pre))){
						hasSimulatingState = true;
						break;
					}
				}
				if (!hasSimulatingState) {
					return false;
				}
			}
		}
		return true;
	}




	/**
	 * @author Richard Mayr.
	 * Compute iterated jumping delayed/backward simulation relation on a Buchi automaton
	 * @param omega1: a Buchi automaton, la: the lookahead in computing the initial delayed simulation
	 *
	 * @return maximal iterated jumping delayed/backward simulation relation
	 * This relation can be used for quotienting, but does not itself imply language inclusion
	 */

	     public Set<Pair<FAState,FAState>> JumpingDelayedSimRelNBW(FiniteAutomaton omega1, int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		int n_states = all_states.size();
		int n_symbols = alphabet.size();
		FAState[] states = all_states.toArray(new FAState[0]);

		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		boolean[] isInitial = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
			isInitial[i] = states[i].getowner().getInitialState().compareTo(states[i])==0;
		}

		int[][][] pre = new int[n_symbols][n_states][];
		int[][][] post = new int[n_symbols][n_states][];
		int[][] pre_len = new int[n_symbols][n_states];
		int[][] post_len = new int[n_symbols][n_states];

		    // Initialize memory of pre/post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				Set<FAState> next = states[p].getNext(a);
				post_len[s][p]=0;
				if (next != null) post[s][p] = new int[states[p].getNext(a).size()];
				Set<FAState> prev = states[p].getPre(a);
				pre_len[s][p]=0;
				if (prev != null) pre[s][p] = new int[states[p].getPre(a).size()];
			    }
		}

		//state[post[s][q][r]] is in post_s(q) for 0<=r<adj_len[s][q]
		//state[pre[s][q][r]] is in pre_s(q) for 0<=r<adj_len[s][q]
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				Set<FAState> next = states[p].getNext(a);
				if (next != null){
				for(int q=0; q<n_states; q++)		
				{
					if(next.contains(states[q]))
					{
						//if p --a--> q, then p is in pre_a(q), q is in post_a(p) 
						pre[s][q][pre_len[s][q]++] = p;
						post[s][p][post_len[s][p]++] = q;
					}
				}
				}
			    }
		}

		int[][] jump = new int[n_states][n_states];
		int[] jump_len = new int[n_states];
		int[][] acc_jump = new int[n_states][n_states];
		int[] acc_jump_len = new int[n_states];


		boolean[][] W = new boolean[n_states][n_states];
		boolean[][] W2 = new boolean[n_states][n_states];
		int sizeW=n_states;
		int oldsizeW=0;
		int sizeW2=n_states;
		int oldsizeW2=0;

		// Compute lookahead delayed simulation first
		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		// Pre refine up to a given depth. To keep memory use modest, the depth is adjusted.
		int x = delayed_pre_refine(n_states,n_symbols,post,post_len,W,depth_pre_refine(la, n_symbols));
		boolean[][] avoid = new boolean[n_states][n_states];
		boolean changed=true;
		while(changed){
		    delayed_bla_get_avoid(avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		    changed=delayed_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		}
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) W[p][q]=!W[p][q];
		close_transitive(W,n_states);
		get_jump(jump, jump_len, acc_jump, acc_jump_len, W, isFinal, n_states);

		// Initialize as for identity relation
		/*
		for(int p=0; p<n_states; p++){
		    if(isFinal[p]){
			acc_jump_len[p]=1;
			acc_jump[p][0]=p;
			jump_len[p]=0;
		    }
		    else{			
		    jump_len[p]=1;
		    jump[p][0]=p;
		    acc_jump_len[p]=0;
		    }
		}
		*/
		
		while(sizeW > oldsizeW || sizeW2 > oldsizeW2){
    		    get_jumping_backward(W2, jump, jump_len, acc_jump, acc_jump_len, isFinal, isInitial, n_states, n_symbols, pre, pre_len);
    		    oldsizeW2 = sizeW2;
		    sizeW2=get_jump(jump, jump_len, acc_jump, acc_jump_len, W2, isFinal, n_states);
		    oldsizeW = sizeW;
		    get_jumping_delayed(W, jump, jump_len, acc_jump, acc_jump_len, isFinal, n_states, n_symbols, post, post_len);
		    sizeW=get_jump(jump, jump_len, acc_jump, acc_jump_len, W, isFinal, n_states);
		    // System.out.println("Size W: "+sizeW);
		}

		// Debug: W2 should be the transpose of W
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
			if(W[p][q] != W2[q][p]) System.out.println("ERROR: Not transpose!");
		
    		
		// Create final result as set of pairs of states
		
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) 
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		
		return FSim2;
		
	}


/*
private void show_W(String s, boolean[][] W, int n_states){
    System.out.println(s);
    for(int p=0; p<n_states; p++)
	for(int q=0; q<n_states; q++)
	    if(W[p][q]) System.out.println("("+p+","+q+")");
}

private void show_jumps(String s, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int n_states){
    System.out.println(s);
    System.out.println("Jumps");
    for(int p=0; p<n_states; p++)
	for(int j=0; j<jump_len[p]; j++)
	    System.out.println(p+" to "+jump[p][j]);
    System.out.println("Acc Jumps");
    for(int p=0; p<n_states; p++)
	for(int j=0; j<acc_jump_len[p]; j++)
	    System.out.println(p+" to "+acc_jump[p][j]);
}

*/


private void get_jumping_delayed(boolean[][] W, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len){
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
				    W[p][q]=false;

		// Initialize result. This will grow by least fixpoint iteration.
		boolean[][] avoid = new boolean[n_states][n_states];
				    
		boolean changed=true;
		while(changed){
		    changed=false;
		    jumping_get_avoid(jump, jump_len, acc_jump, acc_jump_len, avoid,isFinal,n_states,n_symbols,post,post_len,W);
		    for(int p=0; p<n_states; p++)
			for(int q=0; q<n_states; q++){
			    if(W[p][q]) continue;  // True stays true
			    // Attacker makes acc. trans. Dupl. can't reply or (only reply by non-acc trans. leading into avoid).
			    if(jumping_delayed_acc_attack(jump, jump_len, acc_jump, acc_jump_len, p,q,n_symbols,post,post_len,avoid,W)) { W[p][q]=true; changed=true; continue; }
			    // Attacker forces the game into W, regardless of acceptance here. Or else def. can't even reply.
			    if(jumping_CPre(jump, jump_len, acc_jump, acc_jump_len, p,q,n_symbols,post,post_len,W)) { W[p][q]=true; changed=true; }
			}
		}
		// Now invert to get relation for duplicator
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++) W[p][q]=!W[p][q];
}


	// Aux. code for for delayed simulation

private boolean jumping_trapped(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int s, int q, int a, int[][][] post, int[][] post_len, boolean[][] X)
        {
	    for(int j=0; j<jump_len[q]; j++)
		if(post_len[a][jump[q][j]]>0){
		    for(int r=0; r<post_len[a][jump[q][j]]; r++)
			if(!X[s][post[a][jump[q][j]][r]]) return false;
		}
	    for(int j=0; j<acc_jump_len[q]; j++)
		if(post_len[a][acc_jump[q][j]]>0){
		    for(int r=0; r<post_len[a][acc_jump[q][j]]; r++)
			if(!X[s][post[a][acc_jump[q][j]][r]]) return false;
		}
	    return true;
	}

private boolean jumping_CPre(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int p, int q, int n_symbols, int[][][] post, int[][] post_len, boolean[][] X)
        {
	    for(int a=0; a<n_symbols; a++){
		for(int j=0; j<jump_len[p]; j++)
		if(post_len[a][jump[p][j]]>0){
		    for(int r=0; r<post_len[a][jump[p][j]]; r++) 
			if(jumping_trapped(jump, jump_len, acc_jump, acc_jump_len, post[a][jump[p][j]][r], q, a, post, post_len, X)) return true;
		}
		for(int j=0; j<acc_jump_len[p]; j++)
		if(post_len[a][acc_jump[p][j]]>0){
		    for(int r=0; r<post_len[a][acc_jump[p][j]]; r++) 
			if(jumping_trapped(jump, jump_len, acc_jump, acc_jump_len, post[a][acc_jump[p][j]][r], q, a, post, post_len, X)) return true;
		}
	    }
	    return false;
	}

private void jumping_get_avoid(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] avoid, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W)
        {
	    //System.out.println("Computing getavoid.");
	   for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++) avoid[p][q]=true;
		
		boolean changed=true;
		while(changed){
		    changed=false;
		    //System.out.println("Computing getavoid: Iterating refinement");
		    for(int p=0; p<n_states; p++)
			for(int q=0; q<n_states; q++){
			    if(W[p][q] || !avoid[p][q]) continue; // If W then it stays true. If avoid false then stay false
			    // Obsolete: if(isFinal[q]) { avoid[p][q]=false; changed=true; continue; }
			    // Succeed iff att makes move and def. cannot reply or only by non-acc trans. leading into avoid or by trans/acctrans to W
			    if(!inavoid_jumping_delayed_attack(jump, jump_len, acc_jump, acc_jump_len, p,q,n_symbols,post,post_len,avoid,W)) { avoid[p][q]=false; changed=true; }
			}
		} 
	}


// Succeed iff att makes move and def. cannot reply or only by non-acc trans. leading into avoid. or by trans/acctrans to W
private boolean inavoid_jumping_delayed_attack(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int p, int q, int n_symbols, int[][][] post, int[][]post_len, boolean[][] avoid, boolean[][] W){

	    for(int a=0; a<n_symbols; a++){
		for(int j=0; j<jump_len[p]; j++)
		if(post_len[a][jump[p][j]]>0){
		    for(int r=0; r<post_len[a][jump[p][j]]; r++) 
			if(inavoid_jumping_nonacc_trapped(p, jump, jump_len, acc_jump, acc_jump_len, post[a][jump[p][j]][r], q, a, post, post_len, avoid, W)) return true;
		}
		for(int j=0; j<acc_jump_len[p]; j++)
		if(post_len[a][acc_jump[p][j]]>0){
		    for(int r=0; r<post_len[a][acc_jump[p][j]]; r++) 
			if(inavoid_jumping_nonacc_trapped(p, jump, jump_len, acc_jump, acc_jump_len, post[a][acc_jump[p][j]][r], q, a, post, post_len, avoid, W)) return true;
		}
	    }
	    return false;
}


// Dupl. cannot respond or only by non-acc trans. leading into avoid. or by trans/acctrans to W
private boolean inavoid_jumping_nonacc_trapped(int p, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int s, int q, int a, int[][][] post, int[][] post_len, boolean[][] avoid, boolean [][] W)
        {
	    // Dup. wins by acc jumping trans out of W (out of W implies out of avoid)
    	    for(int j=0; j<acc_jump_len[q]; j++)
		if(post_len[a][acc_jump[q][j]]>0){
		    for(int r=0; r<post_len[a][acc_jump[q][j]]; r++)
			if(!W[s][post[a][acc_jump[q][j]][r]]) return false;
		}

	    // Dup. wins by jumping trans out of avoid
	    for(int j=0; j<jump_len[q]; j++)
		if(post_len[a][jump[q][j]]>0){
		    for(int r=0; r<post_len[a][jump[q][j]]; r++)
			if(!avoid[s][post[a][jump[q][j]][r]]) return false;
		}
	    return true;
	}



// Succeed iff att makes accepting move and def. cannot reply or only by non-acc trans. leading into avoid or any transition leading to W
private boolean jumping_delayed_acc_attack(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int p, int q, int n_symbols, int[][][] post, int[][]post_len, boolean[][] avoid, boolean[][] W){

	    for(int a=0; a<n_symbols; a++){
		for(int j=0; j<acc_jump_len[p]; j++)
		if(post_len[a][acc_jump[p][j]]>0){
		    for(int r=0; r<post_len[a][acc_jump[p][j]]; r++) 
			if(jumping_nonacc_trapped(jump, jump_len, acc_jump, acc_jump_len, post[a][acc_jump[p][j]][r], q, a, post, post_len, avoid, W)) return true;
		}
	    }
	    return false;
}


private boolean jumping_nonacc_trapped(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int s, int q, int a, int[][][] post, int[][] post_len, boolean[][] avoid, boolean[][] W)
        {
    	    // Dup. wins by acc jumping trans out of W (not necessarily out of avoid)
    	    for(int j=0; j<acc_jump_len[q]; j++)
		if(post_len[a][acc_jump[q][j]]>0){
		    for(int r=0; r<post_len[a][acc_jump[q][j]]; r++)
			if(!W[s][post[a][acc_jump[q][j]][r]]) return false;
		}

		    // Note: Out of avoid implies out of W. So the case of acc_jumping reply out of avoid is already covered above.

	    // Dup. wins by jumping trans out of avoid
	    for(int j=0; j<jump_len[q]; j++)
		if(post_len[a][jump[q][j]]>0){
		    for(int r=0; r<post_len[a][jump[q][j]]; r++)
			if(!avoid[s][post[a][jump[q][j]][r]]) return false;
		}
	    return true;
		}


private int get_jump(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, boolean[] isFinal, int n_states){
    int result=0; // How many elements in W are true

    for(int p=0; p<n_states; p++){
	jump_len[p]=0;
	acc_jump_len[p]=0;
	for(int q=0; q<n_states; q++)
	    if(W[p][q] && isFinal[q]){
		acc_jump[p][acc_jump_len[p]++] = q;
		result++;
	    }
	int accepts=acc_jump_len[p];
	for(int q=0; q<n_states; q++)
	    if(W[p][q] && !isFinal[q]){
		result++;
		if(jump_bigger(q,acc_jump[p],accepts,W)) acc_jump[p][acc_jump_len[p]++] = q;
		else jump[p][jump_len[p]++] = q;
	    }
    }
    return result;
}

private boolean jump_bigger(int q, int[] seq, int len, boolean[][] W){

    for(int p=0; p<len; p++)
	if(W[seq[p]][q]) return true;

    return false;
}


private void get_jumping_backward(boolean[][] W, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[] isFinal, boolean[] isInitial, int n_states, int n_symbols, int[][][] pre, int[][] pre_len){

    boolean[] jump_to_init = new boolean[n_states];
    for(int p=0; p<n_states; p++){
	jump_to_init[p]=false;
	for(int i=0; i<jump_len[p] && !jump_to_init[p]; i++) if(isInitial[jump[p][i]]) jump_to_init[p]=true;
	for(int i=0; i<acc_jump_len[p] && !jump_to_init[p]; i++) if(isInitial[acc_jump[p][i]]) jump_to_init[p]=true;
    }

    for(int p=0; p<n_states; p++)
	for(int q=0; q<n_states; q++)
	    W[p][q] = (acc_jump_len[p]==0 || acc_jump_len[q]>0) && (!jump_to_init[p] || jump_to_init[q]);

    boolean changed=true;
    while(changed){
	changed=false;
        for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(!W[p][q]) continue; // false stays false
		if(jumping_attack(jump, jump_len, acc_jump, acc_jump_len, p,q,n_symbols,pre,pre_len,W)) { W[p][q]=false; changed=true; }
	    }
    }
}


private boolean jumping_attack(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int p, int q, int n_symbols, int[][][] pre, int[][] pre_len, boolean[][] X)
        {
	    for(int a=0; a<n_symbols; a++){

		for(int j=0; j<acc_jump_len[p]; j++)
		if(pre_len[a][acc_jump[p][j]]>0){
		    for(int r=0; r<pre_len[a][acc_jump[p][j]]; r++) 
			if(!jumping_acc_defense(jump, jump_len, acc_jump, acc_jump_len, pre[a][acc_jump[p][j]][r], q, a, pre, pre_len, X)) return true;
		}

		for(int j=0; j<jump_len[p]; j++)
		if(pre_len[a][jump[p][j]]>0){
		    for(int r=0; r<pre_len[a][jump[p][j]]; r++) 
			if(!jumping_defense(jump, jump_len, acc_jump, acc_jump_len, pre[a][jump[p][j]][r], q, a, pre, pre_len, X)) return true;
		}

	    }
	    return false;
	}


private boolean jumping_acc_defense(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int s, int q, int a, int[][][] pre, int[][] pre_len, boolean[][] X)
        {
	    for(int j=0; j<acc_jump_len[q]; j++)
		if(pre_len[a][acc_jump[q][j]]>0){
		    for(int r=0; r<pre_len[a][acc_jump[q][j]]; r++)
			if(X[s][pre[a][acc_jump[q][j]][r]]) return true;
		}
	    return false;
	}

private boolean jumping_defense(int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int s, int q, int a, int[][][] pre, int[][] pre_len, boolean[][] X)
        {
	    for(int j=0; j<jump_len[q]; j++)
		if(pre_len[a][jump[q][j]]>0){
		    for(int r=0; r<pre_len[a][jump[q][j]]; r++)
			if(X[s][pre[a][jump[q][j]][r]]) return true;
		}
	    for(int j=0; j<acc_jump_len[q]; j++)
		if(pre_len[a][acc_jump[q][j]]>0){
		    for(int r=0; r<pre_len[a][acc_jump[q][j]]; r++)
			if(X[s][pre[a][acc_jump[q][j]][r]]) return true;
		}
	    return false;
	}




	/**
	 * @author Richard Mayr.
	 * Compute iterated jumping direct/backward simulation relation on a Buchi/Finite automaton
	 * @param omega1: a Buchi/Finite automaton, la: the lookahead in computing the initial direct simulation
	 *
	 * @return maximal iterated jumping direct/backward simulation relation
	 * This relation can be used for quotienting, but does not itself imply language inclusion
	 */

	     public Set<Pair<FAState,FAState>> JumpingDirectSimRelNBW(FiniteAutomaton omega1, int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		int n_states = all_states.size();
		int n_symbols = alphabet.size();
		FAState[] states = all_states.toArray(new FAState[0]);

		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		boolean[] isInitial = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
			isInitial[i] = states[i].getowner().getInitialState().compareTo(states[i])==0;
		}

		int[][][] pre = new int[n_symbols][n_states][];
		int[][][] post = new int[n_symbols][n_states][];
		int[][] pre_len = new int[n_symbols][n_states];
		int[][] post_len = new int[n_symbols][n_states];

		    // Initialize memory of pre/post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				Set<FAState> next = states[p].getNext(a);
				post_len[s][p]=0;
				if (next != null) post[s][p] = new int[states[p].getNext(a).size()];
				Set<FAState> prev = states[p].getPre(a);
				pre_len[s][p]=0;
				if (prev != null) pre[s][p] = new int[states[p].getPre(a).size()];
			    }
		}

		//state[post[s][q][r]] is in post_s(q) for 0<=r<adj_len[s][q]
		//state[pre[s][q][r]] is in pre_s(q) for 0<=r<adj_len[s][q]
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n_states; p++){
				Set<FAState> next = states[p].getNext(a);
				if (next != null){
				for(int q=0; q<n_states; q++)		
				{
					if(next.contains(states[q]))
					{
						//if p --a--> q, then p is in pre_a(q), q is in post_a(p) 
						pre[s][q][pre_len[s][q]++] = p;
						post[s][p][post_len[s][p]++] = q;
					}
				}
				}
			    }
		}

		int[][] jump = new int[n_states][n_states];
		int[] jump_len = new int[n_states];
		int[][] acc_jump = new int[n_states][n_states];
		int[] acc_jump_len = new int[n_states];


		boolean[][] W = new boolean[n_states][n_states];
		boolean[][] W2 = new boolean[n_states][n_states];
		int sizeW=n_states;
		int oldsizeW=0;
		int sizeW2=n_states;
		int oldsizeW2=0;

		// compute lookahead direct simulation with lookahead la
		// Initialize result. This will shrink by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			if(isFinal[p] && !isFinal[q]) { W[p][q]=false; continue; }
			W[p][q]=true;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=false; // p can do action s, but q cannot
		    }

		// Pre refine up to a given depth. To keep memory use modest, the depth is adjusted.
		int x = acc_pre_refine(n_states,n_symbols,post,post_len,W,isFinal,depth_pre_refine(la, n_symbols));		
		boolean changed=true;
		while(changed){
		    changed=unref_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,la);
		}
		// Compute transitive closure
		close_transitive(W,n_states);
		get_jump(jump, jump_len, acc_jump, acc_jump_len, W, isFinal, n_states);

		while(sizeW > oldsizeW || sizeW2 > oldsizeW2){
    		    get_jumping_backward(W2, jump, jump_len, acc_jump, acc_jump_len, isFinal, isInitial, n_states, n_symbols, pre, pre_len);
    		    oldsizeW2 = sizeW2;
		    sizeW2=get_jump(jump, jump_len, acc_jump, acc_jump_len, W2, isFinal, n_states);
		    oldsizeW = sizeW;
		    get_jumping_direct(W, jump, jump_len, acc_jump, acc_jump_len, isFinal, n_states, n_symbols, post, post_len);
		    sizeW=get_jump(jump, jump_len, acc_jump, acc_jump_len, W, isFinal, n_states);
		    // System.out.println("Size W: "+sizeW);
		}

		// Debug: W2 should be the transpose of W
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
			if(W[p][q] != W2[q][p]) System.out.println("ERROR: Not transpose!");
		
    		
		// Create final result as set of pairs of states
		
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) 
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		
		return FSim2;
		
	}


private void get_jumping_direct(boolean[][] W, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len){

    for(int p=0; p<n_states; p++)
	for(int q=0; q<n_states; q++)
	    W[p][q] = (acc_jump_len[p]==0 || acc_jump_len[q]>0);

    boolean changed=true;
    while(changed){
	changed=false;
        for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(!W[p][q]) continue; // false stays false
		if(jumping_attack(jump, jump_len, acc_jump, acc_jump_len, p,q,n_symbols,post,post_len,W)) { W[p][q]=false; changed=true; }
	    }
    }
}



// --------------------------------------------------------------------------------------------------



	/**
	 * Compute jumping BLA fair forward simulation relation between the initial states of two Buchi automata
	 * @param omega1, omega2: two Buchi automata
	 * @param la: integer >=1, the lookahead
	 * @param bwchoice: 0=no jumping, 1=jumping w.r.t. bla bw sim, 2=jumping w.r.t. bla counting bw sim, 3=jumping w.r.t. bla segmented bw sim, 
	 * @param 4=transitive closure of bla fair sim without jumping (this should subsume 1, but is slower to compute).
	 *
	 * @return true iff the initial state of omega2 can simulate the initial state of omega1. (For other states it does not mean much).
	 * Advice: Use this only after omega1/omega2 have been minimized with other techniques. Otherwise the high branching degree 
	 * of jumps makes higher lookaheads difficult to compute.
	 */

	     public boolean JumpingBLAFairSimRelNBW(FiniteAutomaton omega1, FiniteAutomaton omega2, int la, int bwchoice) 
	{
	    // Special base bwchoice=4. Use other alg. that computed transitve closeure of whose fair relation
	    if(bwchoice==4){
		Set<Pair<FAState, FAState>> bla_frel;
		bla_frel=BLAFairSimRelNBW(omega1, omega2, la);
		return(bla_frel.contains(new Pair<FAState, FAState>(omega1.getInitialState(), omega2.getInitialState())));
	    }

		ArrayList<FAState> all_states1=new ArrayList<FAState>();
		ArrayList<FAState> all_states2=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states1.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);
		all_states2.addAll(omega2.states);
		alphabet.addAll(omega2.alphabet);

		int n1 = all_states1.size();
		int n2 = all_states2.size();
		int n_symbols = alphabet.size();
		FAState[] states1 = all_states1.toArray(new FAState[0]);
		FAState[] states2 = all_states2.toArray(new FAState[0]);

		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal1 = new boolean[n1];
		boolean[] isFinal2 = new boolean[n2];
		// These give the numbers of the initial states. Only one for each automaton.
		int initial1=0;
		int initial2=0;
		for(int i=0; i<n1; i++){			
			isFinal1[i] = states1[i].getowner().F.contains(states1[i]);
			if(omega1.getInitialState().compareTo(states1[i])==0) initial1=i;
		}
		for(int i=0; i<n2; i++){			
			isFinal2[i] = states2[i].getowner().F.contains(states2[i]);
			if(omega2.getInitialState().compareTo(states2[i])==0) initial2=i;
		}

		int[][][] post1 = new int[n_symbols][n1][];
		int[][] post_len1 = new int[n_symbols][n1];
		int[][][] post2 = new int[n_symbols][n2][];
		int[][] post_len2 = new int[n_symbols][n2];

		    // Initialize memory of post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n1; p++){
				Set<FAState> next = states1[p].getNext(a);
				post_len1[s][p]=0;
				if (next != null) post1[s][p] = new int[states1[p].getNext(a).size()];
			    }
			    for(int p=0; p<n2; p++){
				Set<FAState> next = states2[p].getNext(a);
				post_len2[s][p]=0;
				if (next != null) post2[s][p] = new int[states2[p].getNext(a).size()];
			    }
		}
		// Initialize post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n1; p++){
				Set<FAState> next = states1[p].getNext(a);
				if (next != null){
				for(int q=0; q<n1; q++)		
				{
					if(next.contains(states1[q])) post1[s][p][post_len1[s][p]++] = q;
				}
				}
			    }
			    for(int p=0; p<n2; p++){
				Set<FAState> next = states2[p].getNext(a);
				if (next != null){
				for(int q=0; q<n2; q++)		
				{
					if(next.contains(states2[q])) post2[s][p][post_len2[s][p]++] = q;
				}
				}
			    }
		}

		int[][] jump = new int[n2][n2];
		int[] jump_len = new int[n2];
		int[][] acc_jump = new int[n2][n2];
		int[] acc_jump_len = new int[n2];

		boolean[][] W = new boolean[n1][n2];
		boolean[][] avoid = new boolean[n1][n2];

		// Compute BLA backward sim on omega2 for later jumps, depending on bwchoice parameter.
		{
		boolean[][] jumpmatrix = new boolean[n2][n2];
		if(bwchoice==3){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = Segment_BLABSimRelNBW(omega2, null, la);
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states2[p], states2[q]));
		}
		else if(bwchoice==2){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = C_BLABSimRelNBW(omega2, null, la);
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states2[p], states2[q]));
		}
		else if(bwchoice==1){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = BLABSimRelNBW(omega2, null, la);
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states2[p], states2[q]));
		}
		else if(bwchoice==0){
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=(p==q);
		}
		else{
		    System.out.println("Wrong bwchoice parameter specified, must be in [0,3].");
		    return false;
		}
		
		get_jump(jump, jump_len, acc_jump, acc_jump_len, jumpmatrix, isFinal2, n2);
		}

		// Initialize W as false for the main loop. This will grow (more states winning for spoiler) until fixpoint reached
		// Exception: where spoiler can do an action that duplicator cannot do (even with jumping), then make it winning for spoiler.
		for(int p=0; p<n1; p++)
		    for(int q=0; q<n2; q++){
			W[p][q]=false;			
			for(int s=0;s<n_symbols;s++)
			    if(post_len1[s][p]>0 && !can_jumping_do(s,q,jump,jump_len,acc_jump,acc_jump_len,post_len2)) { W[p][q]=true; }
		    }

		
		boolean changed=true;
		while(changed){
		    // System.out.println("Computing JumpingBLAFair getavoid.");
		    changed=false;
		    JumpingBLAFair_getavoid(isFinal1,isFinal2,n1,n2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,avoid,la);
		    // Copy avoid to W
		    for(int p=0; p<n1; p++)
			for(int q=0; q<n2; q++)
			    if(avoid[p][q] && !W[p][q]) { W[p][q]=true; changed=true; }
		    // Add pairs where spoiler can force the game into W
		    // System.out.println("Refining JumpingBLAFair.");
		    if(JumpingBLAFair_refine_W(n1,n2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,la)) changed=true;
		    // If spoiler is winning then return false
		    if(W[initial1][initial2]) return false;
		}

		// If the result where false then it would have returned false earlier

		// This is just for debugging
		// int size=0;
		// for(int p=0; p<n1; p++)
		//    for(int q=0; q<n2; q++) if(W[p][q]) size++;
		// System.out.println("JumpingBLAFair: Final spoiler relation at end: "+size);

		return true;
	}


                private boolean can_jumping_do(int s, int q, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] post_len2){
			for(int r=0; r<jump_len[q]; r++)
			    if(post_len2[s][jump[q][r]] >0) return true;
			for(int r=0; r<acc_jump_len[q]; r++)
			    if(post_len2[s][acc_jump[q][r]] >0) return true;
		        return false;
		}


private boolean JumpingBLAFair_refine_W(int n1, int n2, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n1; p++)	
	    for(int q=0; q<n2; q++){
		if(W[p][q]) continue; // true remains true;
		attack[0]=p;
		if(JumpingBLAFair_attack(q,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,la,attack,0)) { W[p][q]=true; changed=true; }
	    }
	return changed;
    }


private boolean JumpingBLAFair_attack(int q, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!JumpingBLAFair_defense(q,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,la,attack,0)); 
    
    if (depth > 0){
	if(JumpingBLAFair_defense(q,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,(depth/2),attack,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len1[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!JumpingBLAFair_defense(q,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,(depth/2),attack,0));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len1[s][attack[depth]]>0){
	    for(int r=0; r<post_len1[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post1[s][attack[depth]][r];
		if(JumpingBLAFair_attack(q,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private boolean JumpingBLAFair_defense(int q, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, int la, int[] attack, int depth)
{
    if((depth >0) && !W[attack[depth]][q]) return true; 
    if(depth==2*la) return(!W[attack[depth]][q]);
    int s=attack[depth+1];
    for(int j=0; j<jump_len[q]; j++)
	if(post_len2[s][jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][jump[q][j]]; r++)
		if(JumpingBLAFair_defense(post2[s][jump[q][j]][r],post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,la,attack,depth+2)) return true;
	}
    for(int j=0; j<acc_jump_len[q]; j++)
	if(post_len2[s][acc_jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][acc_jump[q][j]]; r++)
		if(JumpingBLAFair_defense(post2[s][acc_jump[q][j]][r],post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,la,attack,depth+2)) return true;
	}
    return false;
}



private void JumpingBLAFair_getavoid(boolean[] isFinal1, boolean[] isFinal2, int n1, int n2, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, boolean[][] X, int la){

boolean[][] Y = new boolean[n1][n2];
int[] attack = new int[2*la+1];

// Start with X (i.e., avoid) as true and refine downward
for(int p=0; p<n1; p++)
    for(int q=0; q<n2; q++)
	X[p][q]=true;
		
boolean changed_x=true;
while(changed_x){
    changed_x=false;
    // Y is at least W and refined upward
    for(int p=0; p<n1; p++)
	for(int q=0; q<n2; q++) Y[p][q]=W[p][q];
    boolean changed_y=true;
    while(changed_y){
	changed_y=false;
	for(int p=0; p<n1; p++)
	    for(int q=0; q<n2; q++){
		if(Y[p][q]) continue; // If Y true then stay true
		if(isFinal2[q]) continue; // In getavoid duplicator can't accept, except in W (the part of Y in W is already true; see above)
		attack[0]=p;
		if(JumpingBLAFair_getavoid_attack(q,isFinal1,isFinal2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,la,attack,0))  { Y[p][q]=true; changed_y=true; }
	    }
    }
    // X becomes Y, i.e., remove true elements of X that are not true in Y
    for(int p=0; p<n1; p++)
	for(int q=0; q<n2; q++){
	    if(X[p][q] && !Y[p][q]) { X[p][q]=false; changed_x=true; }
	}
}
}


private boolean JumpingBLAFair_getavoid_attack(int q, boolean[] isFinal1, boolean[] isFinal2, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, boolean[][] X, boolean[][] Y, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!JumpingBLAFair_getavoid_defense(q,isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,la,attack,0,false)); 
    
    if (depth > 0){
	if(JumpingBLAFair_getavoid_defense(q,isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,(depth/2),attack,0,false)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len1[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!JumpingBLAFair_getavoid_defense(q,isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,(depth/2),attack,0,false));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len1[s][attack[depth]]>0){
	    for(int r=0; r<post_len1[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post1[s][attack[depth]][r];
		if(JumpingBLAFair_getavoid_attack(q,isFinal1,isFinal2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}


private boolean JumpingBLAFair_getavoid_defense(int q, boolean[] isFinal1, boolean[] isFinal2, int n_symbols, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, boolean[][] W, boolean[][] X, boolean[][] Y, int la, int[] attack, int depth, boolean acc)
{
    if((isFinal2[q]) && !W[attack[depth]][q]) return true;

    if(isFinal1[attack[depth]]) acc=true;
    if(depth>0){
	boolean result=true;
	if(Y[attack[depth]][q]) result=false; 
	if(acc && X[attack[depth]][q]) result=false;
	if(result) return true;
	if(depth==2*la) return result;
    }

    int s=attack[depth+1];

    for(int j=0; j<acc_jump_len[q]; j++)
	if(post_len2[s][acc_jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][acc_jump[q][j]]; r++){
		if(!W[attack[depth+2]][post2[s][acc_jump[q][j]][r]]) return true;
		// Is the next line needed? W is winning for spoiler anyway.
		if(JumpingBLAFair_getavoid_defense(post2[s][acc_jump[q][j]][r],isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,la,attack,depth+2,acc)) return true;
	    }
	}

    for(int j=0; j<jump_len[q]; j++)
	if(post_len2[s][jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][jump[q][j]]; r++)
		if(JumpingBLAFair_getavoid_defense(post2[s][jump[q][j]][r],isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,W,X,Y,la,attack,depth+2,acc)) return true;
	}

    return false;
}


// ---------------------------------------------------------------------------------------------------------------------------------------------


	/**
	 * Compute super-jumping BLA fair forward simulation relation between the initial states of two Buchi automata
	 * @param omega1, omega2: two Buchi automata
	 * @param la: integer >=1, the lookahead
	 * @param bwchoice: 0 does not use jumps, 1 uses bla bw direct sim, 2 use bla bw counting sim.
	 *
	 * @return true iff the initial state of omega2 can simulate the initial state of omega1. (For other states it does not mean much).
	 * Advice: Use this only after omega1/omega2 have been minimized with other techniques. Otherwise the high branching degree 
	 * of jumps makes higher lookaheads difficult to compute.
	 */

	     public boolean x_JumpingBLAFairSimRelNBW(FiniteAutomaton omega1, FiniteAutomaton omega2, int la, int bwchoice) 
	{
		ArrayList<FAState> all_states1=new ArrayList<FAState>();
		ArrayList<FAState> all_states2=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states1.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);
		all_states2.addAll(omega2.states);
		alphabet.addAll(omega2.alphabet);

		int n1 = all_states1.size();
		int n2 = all_states2.size();
		int n_symbols = alphabet.size();
		FAState[] states1 = all_states1.toArray(new FAState[0]);
		FAState[] states2 = all_states2.toArray(new FAState[0]);

		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal1 = new boolean[n1];
		boolean[] isFinal2 = new boolean[n2];
		// These give the numbers of the initial states. Only one for each automaton.
		int initial1=0;
		int initial2=0;
		for(int i=0; i<n1; i++){			
			isFinal1[i] = states1[i].getowner().F.contains(states1[i]);
			if(omega1.getInitialState().compareTo(states1[i])==0) initial1=i;
		}
		for(int i=0; i<n2; i++){			
			isFinal2[i] = states2[i].getowner().F.contains(states2[i]);
			if(omega2.getInitialState().compareTo(states2[i])==0) initial2=i;
		}

		int[][][] post1 = new int[n_symbols][n1][];
		int[][] post_len1 = new int[n_symbols][n1];
		int[][][] post2 = new int[n_symbols][n2][];
		int[][] post_len2 = new int[n_symbols][n2];

		    // Initialize memory of post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n1; p++){
				Set<FAState> next = states1[p].getNext(a);
				post_len1[s][p]=0;
				if (next != null) post1[s][p] = new int[states1[p].getNext(a).size()];
			    }
			    for(int p=0; p<n2; p++){
				Set<FAState> next = states2[p].getNext(a);
				post_len2[s][p]=0;
				if (next != null) post2[s][p] = new int[states2[p].getNext(a).size()];
			    }
		}
		// Initialize post
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			    for(int p=0; p<n1; p++){
				Set<FAState> next = states1[p].getNext(a);
				if (next != null){
				for(int q=0; q<n1; q++)		
				{
					if(next.contains(states1[q])) post1[s][p][post_len1[s][p]++] = q;
				}
				}
			    }
			    for(int p=0; p<n2; p++){
				Set<FAState> next = states2[p].getNext(a);
				if (next != null){
				for(int q=0; q<n2; q++)		
				{
					if(next.contains(states2[q])) post2[s][p][post_len2[s][p]++] = q;
				}
				}
			    }
		}

		int[][] jump = new int[n2][n2];
		int[] jump_len = new int[n2];
		int[][] acc_jump = new int[n2][n2];
		int[] acc_jump_len = new int[n2];
		
		int[][] x_jump = new int[n1][n2];
		int[] x_jump_len = new int[n1];
		int[][] x_acc_jump = new int[n1][n2];
		int[] x_acc_jump_len = new int[n1];

		boolean[][] W = new boolean[n1][n2];
		boolean[][] avoid = new boolean[n1][n2];

		// Compute BLA backward sim on omega2 for later jumps, depending on bwchoice parameter.
		{
		boolean[][] jumpmatrix = new boolean[n2][n2];
		if(bwchoice==3){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = Segment_BLABSimRelNBW(omega2, null, la);
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states2[p], states2[q]));
		}
		else if(bwchoice==2){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = C_BLABSimRelNBW(omega2, null, la);
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states2[p], states2[q]));
		}
		else if(bwchoice==1){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = BLABSimRelNBW(omega2, null, la);
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states2[p], states2[q]));
		}
		else if(bwchoice==0){
		    for(int p=0; p<n2; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=(p==q);
		}
		else{
		    System.out.println("Wrong bwchoice parameter specified, must be in [0,3].");
		    return false;
		}
		
		get_jump(jump, jump_len, acc_jump, acc_jump_len, jumpmatrix, isFinal2, n2);
		}


		// Now compute the same as above, but for x_jumps, again depending on bwchoice parameter.
		{
		boolean[][] jumpmatrix = new boolean[n1][n2];
		if(bwchoice==3){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = Segment_BLABSimRelNBW(omega1, omega2, la);
		    for(int p=0; p<n1; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states1[p], states2[q]));
		}
		else if(bwchoice==2){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = C_BLABSimRelNBW(omega1, omega2, la);
		    for(int p=0; p<n1; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states1[p], states2[q]));
		}
		else if(bwchoice==1){
		    Set<Pair<FAState,FAState>> jumpsim;
		    jumpsim = BLABSimRelNBW(omega1, omega2, la);
		    for(int p=0; p<n1; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=jumpsim.contains(new Pair<FAState,FAState>(states1[p], states2[q]));
		}
		else if(bwchoice==0){
		    for(int p=0; p<n1; p++)
			for(int q=0; q<n2; q++)
			    jumpmatrix[p][q]=false;
		}
		else{
		    System.out.println("Wrong bwchoice parameter specified, must be in [0,3].");
		    return false;
		}
		
		int xjumps = x_get_jump(x_jump, x_jump_len, x_acc_jump, x_acc_jump_len, jumpmatrix, isFinal2, n1, n2);
		//System.out.println(xjumps+" xjumps.");
		}

		/* Debug only
		int extraj=0;
		for(int i=0; i<n1; i++)
		    for(int j=0; j<n2; j++){
			for(int k=0; k<x_acc_jump_len[i]; k++){
			    boolean present=false;
			    for(int l=0; l<acc_jump_len[j]; l++)
				if(acc_jump[j][l]==x_acc_jump[i][k]) present=true;
			    for(int l=0; l<jump_len[j]; l++)
				if(jump[j][l]==x_acc_jump[i][k]) present=true;
			    if(!present) extraj++;
			}
		    }
		System.out.println(extraj+" extra jumps.");
		*/	
		
		

		// Initialize W as false for the main loop. This will grow (more states winning for spoiler) until fixpoint reached
		// Exception: where spoiler can do an action that duplicator cannot do (even with jumping), then make it winning for spoiler.
		for(int p=0; p<n1; p++)
		    for(int q=0; q<n2; q++){
			W[p][q]=false;			
			for(int s=0;s<n_symbols;s++)
			    if(post_len1[s][p]>0 && !x_can_jumping_do(s,p,q,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,post_len2)) { W[p][q]=true; }
		    }

		
		boolean changed=true;
		while(changed){
		    // System.out.println("Computing JumpingBLAFair getavoid.");
		    changed=false;
		    x_JumpingBLAFair_getavoid(isFinal1,isFinal2,n1,n2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,avoid,la);
		    // Copy avoid to W
		    for(int p=0; p<n1; p++)
			for(int q=0; q<n2; q++)
			    if(avoid[p][q] && !W[p][q]) { W[p][q]=true; changed=true; }
		    // Add pairs where spoiler can force the game into W
		    // System.out.println("Refining JumpingBLAFair.");
		    if(x_JumpingBLAFair_refine_W(n1,n2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la)) changed=true;
		    // If spoiler is winning then return false
		    if(W[initial1][initial2]) return false;
		}

		// If the result where false then it would have returned false earlier

		// This is just for debugging
		// int size=0;
		// for(int p=0; p<n1; p++)
		//    for(int q=0; q<n2; q++) if(W[p][q]) size++;
		// System.out.println("JumpingBLAFair: Final spoiler relation at end: "+size);

		return true;
	}


private boolean x_can_jumping_do(int s, int p, int q, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, int[][] post_len2){
			for(int r=0; r<jump_len[q]; r++)
			    if(post_len2[s][jump[q][r]] >0) return true;
			for(int r=0; r<acc_jump_len[q]; r++)
			    if(post_len2[s][acc_jump[q][r]] >0) return true;

			for(int r=0; r<x_jump_len[p]; r++)
			    if(post_len2[s][x_jump[p][r]] >0) return true;
			for(int r=0; r<x_acc_jump_len[p]; r++)
			    if(post_len2[s][x_acc_jump[p][r]] >0) return true;

		        return false;
		}


private boolean x_JumpingBLAFair_refine_W(int n1, int n2, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n1; p++)	
	    for(int q=0; q<n2; q++){
		if(W[p][q]) continue; // true remains true;
		attack[0]=p;
		if(x_JumpingBLAFair_attack(q,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,0)) { W[p][q]=true; changed=true; }
	    }
	return changed;
    }


private boolean x_JumpingBLAFair_attack(int q, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!x_JumpingBLAFair_defense(q,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,0)); 
    
    if (depth > 0){
	if(x_JumpingBLAFair_defense(q,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,(depth/2),attack,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len1[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!x_JumpingBLAFair_defense(q,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,(depth/2),attack,0));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len1[s][attack[depth]]>0){
	    for(int r=0; r<post_len1[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post1[s][attack[depth]][r];
		if(x_JumpingBLAFair_attack(q,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private boolean x_JumpingBLAFair_defense(int q, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, int la, int[] attack, int depth)
{
    if((depth >0) && !W[attack[depth]][q]) return true; 
    if(depth==2*la) return(!W[attack[depth]][q]);
    int s=attack[depth+1];
    for(int j=0; j<jump_len[q]; j++)
	if(post_len2[s][jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][jump[q][j]]; r++)
		if(x_JumpingBLAFair_defense(post2[s][jump[q][j]][r],post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,depth+2)) return true;
	}
    for(int j=0; j<acc_jump_len[q]; j++)
	if(post_len2[s][acc_jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][acc_jump[q][j]]; r++)
		if(x_JumpingBLAFair_defense(post2[s][acc_jump[q][j]][r],post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,depth+2)) return true;
	}
    for(int j=0; j<x_jump_len[attack[depth]]; j++)
	if(post_len2[s][x_jump[attack[depth]][j]]>0){
	    for(int r=0; r<post_len2[s][x_jump[attack[depth]][j]]; r++)
		if(x_JumpingBLAFair_defense(post2[s][x_jump[attack[depth]][j]][r],post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,depth+2)) { /* System.out.println("X-jumping helped"); */ return true; }
	}
    for(int j=0; j<x_acc_jump_len[attack[depth]]; j++)
	if(post_len2[s][x_acc_jump[attack[depth]][j]]>0){
	    for(int r=0; r<post_len2[s][x_acc_jump[attack[depth]][j]]; r++)
		if(x_JumpingBLAFair_defense(post2[s][x_acc_jump[attack[depth]][j]][r],post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,la,attack,depth+2)) { /* System.out.println("X-jumping helped"); */ return true; }
	}

    return false;
}



private void x_JumpingBLAFair_getavoid(boolean[] isFinal1, boolean[] isFinal2, int n1, int n2, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, boolean[][] X, int la){

boolean[][] Y = new boolean[n1][n2];
int[] attack = new int[2*la+1];

// Start with X (i.e., avoid) as true and refine downward
for(int p=0; p<n1; p++)
    for(int q=0; q<n2; q++)
	X[p][q]=true;
		
boolean changed_x=true;
while(changed_x){
    changed_x=false;
    // Y is at least W and refined upward
    for(int p=0; p<n1; p++)
	for(int q=0; q<n2; q++) Y[p][q]=W[p][q];
    boolean changed_y=true;
    while(changed_y){
	changed_y=false;
	for(int p=0; p<n1; p++)
	    for(int q=0; q<n2; q++){
		if(Y[p][q]) continue; // If Y true then stay true
		if(isFinal2[q]) continue; // In getavoid duplicator can't accept, except in W (the part of Y in W is already true; see above)
		attack[0]=p;
		if(x_JumpingBLAFair_getavoid_attack(q,isFinal1,isFinal2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,0))  { Y[p][q]=true; changed_y=true; }
	    }
    }
    // X becomes Y, i.e., remove true elements of X that are not true in Y
    for(int p=0; p<n1; p++)
	for(int q=0; q<n2; q++){
	    if(X[p][q] && !Y[p][q]) { X[p][q]=false; changed_x=true; }
	}
}
}


private boolean x_JumpingBLAFair_getavoid_attack(int q, boolean[] isFinal1, boolean[] isFinal2, int n_symbols, int[][][] post1, int[][] post_len1, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, boolean[][] X, boolean[][] Y, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!x_JumpingBLAFair_getavoid_defense(q,isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,0,false)); 
    
    if (depth > 0){
	if(x_JumpingBLAFair_getavoid_defense(q,isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,(depth/2),attack,0,false)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len1[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!x_JumpingBLAFair_getavoid_defense(q,isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,(depth/2),attack,0,false));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len1[s][attack[depth]]>0){
	    for(int r=0; r<post_len1[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post1[s][attack[depth]][r];
		if(x_JumpingBLAFair_getavoid_attack(q,isFinal1,isFinal2,n_symbols,post1,post_len1,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}


private boolean x_JumpingBLAFair_getavoid_defense(int q, boolean[] isFinal1, boolean[] isFinal2, int n_symbols, int[][][] post2, int[][] post_len2, int[][] jump, int[] jump_len, int[][] acc_jump, int[] acc_jump_len, int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, boolean[][] X, boolean[][] Y, int la, int[] attack, int depth, boolean acc)
{
    if((isFinal2[q]) && !W[attack[depth]][q]) return true;

    if(isFinal1[attack[depth]]) acc=true;
    if(depth>0){
	boolean result=true;
	if(Y[attack[depth]][q]) result=false; 
	if(acc && X[attack[depth]][q]) result=false;
	if(result) return true;
	if(depth==2*la) return result;
    }

    int s=attack[depth+1];

    for(int j=0; j<acc_jump_len[q]; j++)
	if(post_len2[s][acc_jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][acc_jump[q][j]]; r++){
		if(!W[attack[depth+2]][post2[s][acc_jump[q][j]][r]]) return true;
		// Is the next line needed? W is winning for spoiler anyway.
		if(x_JumpingBLAFair_getavoid_defense(post2[s][acc_jump[q][j]][r],isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,depth+2,acc)) return true;
	    }
	}

    for(int j=0; j<jump_len[q]; j++)
	if(post_len2[s][jump[q][j]]>0){
	    for(int r=0; r<post_len2[s][jump[q][j]]; r++)
		if(x_JumpingBLAFair_getavoid_defense(post2[s][jump[q][j]][r],isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,depth+2,acc)) return true;
	}

    for(int j=0; j<x_acc_jump_len[attack[depth]]; j++)
	if(post_len2[s][x_acc_jump[attack[depth]][j]]>0){
	    for(int r=0; r<post_len2[s][x_acc_jump[attack[depth]][j]]; r++){
		if(!W[attack[depth+2]][post2[s][x_acc_jump[attack[depth]][j]][r]]) { /* System.out.println("X-jumping helped in getavoid."); */ return true; }
		// Is the next line needed? W is winning for spoiler anyway.
		if(x_JumpingBLAFair_getavoid_defense(post2[s][x_acc_jump[attack[depth]][j]][r],isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,depth+2,acc)) return true;
	    }
	}
    for(int j=0; j<x_jump_len[attack[depth]]; j++)
	if(post_len2[s][x_jump[attack[depth]][j]]>0){
	    for(int r=0; r<post_len2[s][x_jump[attack[depth]][j]]; r++)
		if(x_JumpingBLAFair_getavoid_defense(post2[s][x_jump[attack[depth]][j]][r],isFinal1,isFinal2,n_symbols,post2,post_len2,jump,jump_len,acc_jump,acc_jump_len,x_jump,x_jump_len,x_acc_jump,x_acc_jump_len,W,X,Y,la,attack,depth+2,acc)) return true;
	}

    return false;
}



private int x_get_jump(int[][] x_jump, int[] x_jump_len, int[][] x_acc_jump, int[] x_acc_jump_len, boolean[][] W, boolean[] isFinal, int n1, int n2){
    int result=0; // How many elements in W are true

    for(int p=0; p<n1; p++){
	x_jump_len[p]=0;
	x_acc_jump_len[p]=0;
	for(int q=0; q<n2; q++){
	    if(W[p][q] /* && isFinal[q] */){
		x_acc_jump[p][x_acc_jump_len[p]++] = q;
		result++;
	    }
	    /*
	    else if(W[p][q] && !isFinal[q]){
		x_jump[p][x_jump_len[p]++] = q;
		result++;
	    }
	    */
	}
    }
    return result;
}


// ----------------------------------------------------------------------------------------------------------------------------------------------

 	/**
	 * Compute the transitive closure of acc-counting bounded lookahead direct backward simulation on/between two Buchi automata
	 * This is NOT an underapproximation of direct backward trace inclusion.
	 * It only ensures that, if x <= y, then for every bw-path from x to init, there is a bw-path from y to init what accepts at least as often
	 * (but not necessarily at the same time).
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A preorder relation that satisfies the criterion above
	 */

    public Set<Pair<FAState,FAState>> C_BLABSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];
		// Relation must respect initial states, but not exactly the final states.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
			W[p][q]=(((!(states[p].getowner().getInitialState().compareTo(states[p])==0)) || (states[q].getowner().getInitialState().compareTo(states[q])==0)));
		
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		boolean[] isInit = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
			isInit[i] =states[i].getowner().getInitialState().compareTo(states[i])==0;
		}

		// Actually post is initialized as pre, because all is reversed in bw sim.
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
		    // System.out.println("Symbol "+s+" of "+n_symbols);
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getPre(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getPre(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA B sim. Outer iteration.");
		    changed=C_BLAB_refine(isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
		}
		}
		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean C_BLAB_refine(boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n_states; p++)	
	    for(int q=0; q<n_states; q++){
		if(!W[p][q]) continue; // false remains false;
		attack[0]=p;
		if(C_BLAB_attack(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,0)) { W[p][q]=false; changed=true; }
	    }
	return changed;
    }

private boolean C_BLAB_attack(int p, int q, boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!C_BLAB_defense(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,0,0)); 
    
    // if defender can defend against attack so far, then attack fails.
    if (depth > 0){
	if(C_BLAB_defense(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,(depth/2),attack,0,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!C_BLAB_defense(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,(depth/2),attack,0,0));
    }

    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(C_BLAB_attack(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}


private boolean C_BLAB_defense(int p, int q, boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth, int counter)
{
    if(isFinal[attack[depth]]) ++counter;
    if(isFinal[q]) --counter;
    if(isInit[attack[depth]]){
	if(!isInit[q]) return false;
	if(counter>0) return false;
    }
    boolean res = W[attack[depth]][q] && (counter <= 0);

    if((depth >0) && res) return true; 
    if(depth==2*la) return(res);

    int s=attack[depth+1];
    if(post_len[s][q]==0) return(false);
    for(int r=0; r<post_len[s][q]; r++){
	if(C_BLAB_defense(p,post[s][q][r],isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2,counter)) return true;
    }
    return false;
}





// ----------------------------------------------------------------------------------------------------------------------------------------------

 	/**
	 * Compute the transitive closure of segment-accepting bounded lookahead direct backward simulation on/between two Buchi automata
	 * This is NOT an underapproximation of direct backward trace inclusion.
	 * It only ensures that, if x <= y, then for every bw-path from y to init, it accepts at least once every la steps.
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A preorder relation that satisfies the criterion above
	 *
	 * This relation is used optionally in JumpingBLAFairSim. It is incomparable to C_BLAB and normal BLAB.
	 */

    public Set<Pair<FAState,FAState>> Segment_BLABSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];
		// Relation must respect initial states, but not exactly the final states.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
			W[p][q]=(((!(states[p].getowner().getInitialState().compareTo(states[p])==0)) || (states[q].getowner().getInitialState().compareTo(states[q])==0)));
		
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		boolean[] isInit = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
			isInit[i] =states[i].getowner().getInitialState().compareTo(states[i])==0;
		}

		// Actually post is initialized as pre, because all is reversed in bw sim.
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
		    // System.out.println("Symbol "+s+" of "+n_symbols);
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getPre(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getPre(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA B sim. Outer iteration.");
		    changed=Segment_BLAB_refine(isFinal,isInit,n_states,n_symbols,post,post_len,W,la);
		}
		}
		// Segment bw-sim is not itself reflexive. Get the reflexive closure.
		for(int p=0; p<n_states; p++) W[p][p]=true;

		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean Segment_BLAB_refine(boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n_states; p++)	
	    for(int q=0; q<n_states; q++){
		if(!W[p][q]) continue; // false remains false;
		attack[0]=p;
		if(Segment_BLAB_attack(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,0)) { W[p][q]=false; changed=true; }
	    }
	return changed;
    }

private boolean Segment_BLAB_attack(int p, int q, boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!Segment_BLAB_defense(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,0,0)); 
    
    // if defender can defend against attack so far, then attack fails.
    if (depth > 0){
	if(Segment_BLAB_defense(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,(depth/2),attack,0,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!Segment_BLAB_defense(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,(depth/2),attack,0,0));
    }

    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(Segment_BLAB_attack(p,q,isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}


private boolean Segment_BLAB_defense(int p, int q, boolean[] isFinal, boolean[] isInit, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth, int counter)
{
    // Here counter counts (decreasingly), how often duplicator has visited an acc state in his defense round.
    // A defense is only successful if at least one acc state was visited, i.e., counter < 0

    // if(isFinal[attack[depth]]) ++counter;
    if(isFinal[q]) --counter;
    if(isInit[attack[depth]]){
	if(!isInit[q]) return false;
	// if(counter>0) return false;
    }
    boolean res = W[attack[depth]][q] && (counter < 0);

    if((depth >0) && res) return true; 
    if(depth==2*la) return(res);

    int s=attack[depth+1];
    if(post_len[s][q]==0) return(false);
    for(int r=0; r<post_len[s][q]; r++){
	if(Segment_BLAB_defense(p,post[s][q][r],isFinal,isInit,n_states,n_symbols,post,post_len,W,la,attack,depth+2,counter)) return true;
    }
    return false;
}




 	/**
	 * Compute normal backward (resp. forward) direct simulation on/between two Buchi automata.
	 * @param omega1, omega2: two Buchi automata. 
	 *
	 * @return Backward (resp. forward) simulation preorder
	 */

    public Set<Pair<FAState,FAState>> BackwardSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2){
		ArrayList<FAState> all_states = new ArrayList<FAState>();
		HashSet<String> alphabet = new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}
		    
		FAState[] states = all_states.toArray(new FAState[0]);

			boolean[] isFinal = new boolean[states.length];
			boolean[] isInit = new boolean[states.length];
			boolean[][] bsim = new boolean[states.length][states.length];
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
			return FastBSimRelNBW(omega1, omega2, bsim);
	    }



    public Set<Pair<FAState,FAState>> ForwardSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2){
	ArrayList<FAState> all_states = new ArrayList<FAState>();
		HashSet<String> alphabet = new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}
		    
		FAState[] states = all_states.toArray(new FAState[0]);

			boolean[] isFinal = new boolean[states.length];
			boolean[] isInit = new boolean[states.length];
			boolean[][] fsim = new boolean[states.length][states.length];
			for (int i = 0; i < states.length; i++) {
				isFinal[i] = states[i].getowner().F.contains(states[i]);
				isInit[i] = states[i].getowner().getInitialState()
						.compareTo(states[i]) == 0;
			}
			for (int i = 0; i < states.length; i++) {
				for (int j = i; j < states.length; j++) {
					fsim[i][j] =  (!isFinal[i] || isFinal[j])
							&& states[j].fw_covers(states[i]);
					fsim[j][i] =  (isFinal[i] || !isFinal[j])
							&& states[i].fw_covers(states[j]);
				}
			}
			return FastFSimRelNBW(omega1, omega2, fsim);
	    }



	/* This computes a weaker version of backward simulation on/between system 
	   and spec. Unlike normal bw-sim, it does not care about accepting states.
	   This weak relation can only be used for some special purposes in -sp 
	   It cannot replace normal bw-sim.  */ 

	  public Set<Pair<FAState, FAState>> acceptance_blind_BackwardSimRelNBW(FiniteAutomaton omega1, FiniteAutomaton omega2) {
		ArrayList<FAState> all_states = new ArrayList<FAState>();
		HashSet<String> alphabet = new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		all_states.addAll(omega2.states);
		alphabet.addAll(omega2.alphabet);

		FAState[] states = all_states.toArray(new FAState[0]);

			boolean[] isFinal = new boolean[states.length];
			boolean[] isInit = new boolean[states.length];
			boolean[][] bsim = new boolean[states.length][states.length];
			for (int i = 0; i < states.length; i++) {
				isFinal[i] = states[i].getowner().F.contains(states[i]);
				isInit[i] = states[i].getowner().getInitialState()
						.compareTo(states[i]) == 0;
			}
			for (int i = 0; i < states.length; i++) {
				for (int j = i; j < states.length; j++) {
					bsim[i][j] = (!isInit[i] || isInit[j])
							&& states[j].bw_covers(states[i]);
					bsim[j][i] = (isInit[i] || !isInit[j])
							&& states[i].bw_covers(states[j]);
				}
			}
			return FastBSimRelNBW(omega1, omega2, bsim);
	    }





//-----------------------------------------------------------------------------------------------------------------------
	/**
	 * Compute BLA fair forward simulation on/between two Buchi automata
	 * @param omega1, omega2: two Buchi automata
	 * @param la: integer >=1, the lookahead
	 *
	 * @return the transitive closure of the simulation relation
	 * Advice: Use this only for benchmark tests. Otherwise use jumping BLA fair sim.
	 */

	     public Set<Pair<FAState,FAState>> BLAFairSimRelNBW(FiniteAutomaton omega1, FiniteAutomaton omega2, int la) 
	     {
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		boolean[][] W = new boolean[n_states][n_states];

		FAState[] states = all_states.toArray(new FAState[0]);

		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				//System.out.println("Delayed sim: Getting post: Iterating p: "+p+" of "+n_states+" s is "+s+" of "+n_symbols);
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}
		
		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		boolean[][] avoid = new boolean[n_states][n_states];
				    
		boolean changed=true;
		while(changed){
		    // System.out.println("Computing BLAFair getavoid.");
		    changed=false;
		    BLAFair_getavoid(isFinal,n_states,n_symbols,post,post_len,W,avoid,la);
		    // Copy avoid to W
		    for(int p=0; p<n_states; p++)
			for(int q=0; q<n_states; q++)
			    if(avoid[p][q] && !W[p][q]) { W[p][q]=true; changed=true; }
		    // Add pairs where spoiler can force the game into W
		    // System.out.println("Refining BLAFair.");
		    if(BLAFair_refine_W(n_states,n_symbols,post,post_len,W,la)) changed=true;
		}

		// This is just for debugging
		// int size=0;
		// for(int p=0; p<n; p++)
		//    for(int q=0; q<n; q++) if(W[p][q]) size++;
		// System.out.println("BLAFair: Final spoiler relation at end: "+size);

		// Invert to get duplicator winning states
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) W[p][q]=!W[p][q];

		// Compute transitive closure
		close_transitive(W,n_states);
		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}



private boolean BLAFair_refine_W(int n, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n; p++)	
	    for(int q=0; q<n; q++){
		if(W[p][q]) continue; // true remains true;
		attack[0]=p;
		if(BLAFair_attack(q,n_symbols,post,post_len,W,la,attack,0)) { W[p][q]=true; changed=true; }
	    }
	return changed;
    }


private boolean BLAFair_attack(int q, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!BLAFair_defense(q,post,post_len,W,la,attack,0)); 
    
    if (depth > 0){
	if(BLAFair_defense(q,post,post_len,W,(depth/2),attack,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!BLAFair_defense(q,post,post_len,W,(depth/2),attack,0));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(BLAFair_attack(q,n_symbols,post,post_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private boolean BLAFair_defense(int q, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if((depth >0) && !W[attack[depth]][q]) return true; 
    if(depth==2*la) return(!W[attack[depth]][q]);
    int s=attack[depth+1];
    for(int j=0; j<post_len[s][q]; j++)
	if(BLAFair_defense(post[s][q][j],post,post_len,W,la,attack,depth+2)) return true;
    return false;
}



private void BLAFair_getavoid(boolean[] isFinal, int n, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] X, int la){

boolean[][] Y = new boolean[n][n];
int[] attack = new int[2*la+1];

// Start with X (i.e., avoid) as true and refine downward
for(int p=0; p<n; p++)
    for(int q=0; q<n; q++)
	X[p][q]=true;
		
boolean changed_x=true;
while(changed_x){
    changed_x=false;
    // Y is at least W and refined upward
    for(int p=0; p<n; p++)
	for(int q=0; q<n; q++) Y[p][q]=W[p][q];
    boolean changed_y=true;
    while(changed_y){
	changed_y=false;
	for(int p=0; p<n; p++)
	    for(int q=0; q<n; q++){
		if(Y[p][q]) continue; // If Y true then stay true
		if(isFinal[q]) continue; // In getavoid duplicator can't accept, except in W (the part of Y in W is already true; see above)
		attack[0]=p;
		if(BLAFair_getavoid_attack(q,isFinal,n_symbols,post,post_len,W,X,Y,la,attack,0))  { Y[p][q]=true; changed_y=true; }
	    }
    }
    // X becomes Y, i.e., remove true elements of X that are not true in Y
    for(int p=0; p<n; p++)
	for(int q=0; q<n; q++){
	    if(X[p][q] && !Y[p][q]) { X[p][q]=false; changed_x=true; }
	}
}
}


private boolean BLAFair_getavoid_attack(int q, boolean[] isFinal, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] X, boolean[][] Y, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!BLAFair_getavoid_defense(q,isFinal,n_symbols,post,post_len,W,X,Y,la,attack,0,false)); 
    
    if (depth > 0){
	if(BLAFair_getavoid_defense(q,isFinal,n_symbols,post,post_len,W,X,Y,(depth/2),attack,0,false)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!BLAFair_getavoid_defense(q,isFinal,n_symbols,post,post_len,W,X,Y,(depth/2),attack,0,false));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(BLAFair_getavoid_attack(q,isFinal,n_symbols,post,post_len,W,X,Y,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}


private boolean BLAFair_getavoid_defense(int q, boolean[] isFinal, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] X, boolean[][] Y, int la, int[] attack, int depth, boolean acc)
{
    if((isFinal[q]) && !W[attack[depth]][q]) return true;

    if(isFinal[attack[depth]]) acc=true;
    if(depth>0){
	boolean result=true;
	if(Y[attack[depth]][q]) result=false; 
	if(acc && X[attack[depth]][q]) result=false;
	if(result) return true;
	if(depth==2*la) return result;
    }

    int s=attack[depth+1];

    for(int r=0; r<post_len[s][q]; r++){
	if(!W[attack[depth+2]][post[s][q][r]]) return true;
	if(BLAFair_getavoid_defense(post[s][q][r],isFinal,n_symbols,post,post_len,W,X,Y,la,attack,depth+2,acc)) return true;
    }
    return false;
}


// ---------------------------------------------------------------------------------------------------------------------------------------------



	/**
	 * Compute the transitive closure of 2-pebble la-bounded lookahead direct forward simulation on/between two Buchi automata
	 * This is an underapproximation of direct forward trace inclusion.
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A relation that underapproximates direct forward trace inclusion.
	 */

    public Set<Pair<FAState,FAState>> pebble_BLASimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][][] W = new boolean[n_states][n_states][n_states];

		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize acceptance condition for universal direct simulation
		for(int p=0; p<n_states; p++)
		    for(int q1=0; q1<n_states; q1++)
			for(int q2=0; q2<n_states; q2++){
			    if(isFinal[p] && (!isFinal[q1] || !isFinal[q2])) { W[p][q1][q2]=false; continue; }
			    W[p][q1][q2]=true;
			    for(int s=0;s<n_symbols;s++)
				if(post_len[s][p]>0 && post_len[s][q1]==0 && post_len[s][q2]==0) W[p][q1][q2]=false; // p can do action s, neither q1/q2 can
			}

		// Compute all pairs of states that can be reached by 2-pebble splitting from a single state. 	
		//System.out.println("Computing needed pairs.");
		boolean[][] need = new boolean[n_states][n_states];
		for(int i=0; i<n_states; i++) 
		    for(int j=0; j<n_states; j++) need[i][j]=(i==j);
		boolean flag=true;
		while(flag){
		    flag=false;
		    for(int i=0; i<n_states; i++) 
			for(int j=0; j<n_states; j++) if(need[i][j])
							  for(int s=0;s<n_symbols;s++){
							      for(int r1=0; r1<post_len[s][i]; r1++)
								  for(int r2=0; r2<post_len[s][j]; r2++) 
								      if(!need[post[s][i][r1]][post[s][j][r2]]){
									  need[post[s][i][r1]][post[s][j][r2]]=true;
									  flag=true;
								      }
							  }
			    }
		int worth=0;
		for(int p=0; p<n_states; p++)
		    for(int q1=0; q1<n_states; q1++)
			for(int q2=0; q2<n_states; q2++)
			    if(W[p][q1][q2] && !need[q1][q2]){
				W[p][q1][q2]=false;
				worth++;
			    }
		//System.out.println("Removed "+worth+" superfluous entries.");
		
		// Initialize result. This will shrink by least fixpoint iteration.
				    
		boolean changed=true;
		while(changed){
		    // System.out.println("Pebble BLA sim. Outer iteration.");
		    changed=pebble_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,la);
		}
		}
		// Get relation between pairs of states
		boolean[][] W2 = new boolean[n_states][n_states];
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++)
			W2[p][q]=W[p][q][q];
		// Compute transitive closure
		close_transitive(W2,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W2[p][q]) FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean pebble_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n_states; p++)	
	    for(int q1=0; q1<n_states; q1++)
		for(int q2=0; q2<n_states; q2++){
		    if(!W[p][q1][q2]) continue; // false remains false;
		    attack[0]=p;
		    if(pebble_BLA_attack(p,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,la,attack,0)) { W[p][q1][q2]=false; changed=true; }
		}
	return changed;
    }


private boolean pebble_BLA_attack(int p, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (!pebble_BLA_defense(p,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,la,attack,0));
    
    if (depth > 0){
	if(pebble_BLA_defense(p,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,(depth/2),attack,0)) return false;
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(!pebble_BLA_defense(p,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,(depth/2),attack,0));
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(pebble_BLA_attack(p,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private boolean pebble_BLA_defense(int p, int q1, int q2, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][][] W, int la, int[] attack, int depth)
{
    if(isFinal[attack[depth]] && (!isFinal[q1] || !isFinal[q2])) return false;
    if((depth >0) && W[attack[depth]][q1][q2]) return true; 
    if(depth==2*la) return(W[attack[depth]][q1][q2]);
    int s=attack[depth+1];
    if(post_len[s][q1]==0 && post_len[s][q2]==0) return(false);

   // Case: Propagate both q1 and q2
    for(int r1=0; r1<post_len[s][q1]; r1++)
	for(int r2=0; r2<post_len[s][q2]; r2++)
	    if(pebble_BLA_defense(p,post[s][q1][r1],post[s][q2][r2],isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return true;

    // Case: Discard q2, split q1
    for(int r1=0; r1<post_len[s][q1]; r1++)
	for(int r2=0; r2<post_len[s][q1]; r2++)
	    if(pebble_BLA_defense(p,post[s][q1][r1],post[s][q1][r2],isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return true;

    // Case: Discard q1, split q2
    for(int r1=0; r1<post_len[s][q2]; r1++)
	for(int r2=0; r2<post_len[s][q2]; r2++)
	    if(pebble_BLA_defense(p,post[s][q2][r1],post[s][q2][r2],isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return true;

     return false;
}

//-------------------------------------------------------------------------------------------------------------------------------------


	/**
	 * Compute an under-approximation of forward direct trace inclusion on/between two Buchi automata,
	 * by a combination of lookahead simulation and 2-pebble simulation. 
	 * A attempt for a compromise bweteen relation size and efficiency.
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A relation that underapproximates direct forward trace inclusion.
	 */

    public Set<Pair<FAState,FAState>> addpebble_BLASimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];

		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize result. This will shrink by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			if(isFinal[p] && !isFinal[q]) { W[p][q]=false; continue; }
			W[p][q]=true;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=false; // p can do action s, but q cannot
		    }

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA sim. Outer iteration.");
		    changed=unref_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,la);
		}
		
		// Compute transitive closure
		close_transitive(W,n_states);

		boolean[][][] pW = new boolean[n_states][n_states][n_states];
		// Initialize pW for acceptance condition for universal direct simulation
		for(int p=0; p<n_states; p++)
		    for(int q1=0; q1<n_states; q1++)
			for(int q2=0; q2<n_states; q2++){
			    if(isFinal[p] && (!isFinal[q1] || !isFinal[q2])) { pW[p][q1][q2]=false; continue; }
			    pW[p][q1][q2]=true;
			    for(int s=0;s<n_symbols;s++)
				if(post_len[s][p]>0 && post_len[s][q1]==0 && post_len[s][q2]==0) pW[p][q1][q2]=false; // p can do action s, neither q1/q2 can
			}

		// Compute all pairs of states that can be reached by 2-pebble splitting from a single state. 	
		//System.out.println("Computing needed pairs.");
		boolean[][] need = new boolean[n_states][n_states];
		for(int i=0; i<n_states; i++) 
		    for(int j=0; j<n_states; j++) need[i][j]=(i==j);
		boolean flag=true;
		while(flag){
		    flag=false;
		    for(int i=0; i<n_states; i++) 
			for(int j=0; j<n_states; j++) if(need[i][j])
							  for(int s=0;s<n_symbols;s++){
							      for(int r1=0; r1<post_len[s][i]; r1++)
								  for(int r2=0; r2<post_len[s][j]; r2++) 
								      if(!need[post[s][i][r1]][post[s][j][r2]]){
									  need[post[s][i][r1]][post[s][j][r2]]=true;
									  flag=true;
								      }
							  }
			    }
		int worth=0;
		for(int p=0; p<n_states; p++)
		    for(int q1=0; q1<n_states; q1++)
			for(int q2=0; q2<n_states; q2++)
			    if(pW[p][q1][q2] && !need[q1][q2]){
				pW[p][q1][q2]=false;
				worth++;
			    }
		//System.out.println("Addpebble: Removed "+worth+" superfluous entries.");

		changed=true;
		while(changed){
		    // System.out.println("AddPebble BLA sim. Outer iteration.");
		    changed=addpebble_BLA_refine(isFinal,n_states,n_symbols,post,post_len,pW,2,W);
		}
		// Update relation between pairs of states. I.e., update W with info from pW
		worth=0;
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++) if(!W[p][q] && pW[p][q][q]){
			    W[p][q]=true;
			    worth++;
			}
		//System.out.println("Addpebble: Added "+worth+" pairs to relation by 2-pebble sim.");
		// Compute transitive closure
		close_transitive(W,n_states);
		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) // W is winning for duplicator here
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean addpebble_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][][] W, int la, boolean[][] keep)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n_states; p++)	
	    for(int q1=0; q1<n_states; q1++)
		for(int q2=0; q2<n_states; q2++){
		    if(!W[p][q1][q2]) continue; // false remains false;
		    if(keep[p][q1]) continue; // keep protects against removal. Must stay true.
		    if(keep[p][q2]) continue; // keep protects against removal. Must stay true.
		    attack[0]=p;
		    if(pebble_BLA_attack(p,q1,q2,isFinal,n_states,n_symbols,post,post_len,W,la,attack,0)) { W[p][q1][q2]=false; changed=true; }
		}
	return changed;
    }



    //-------------------------------------------- Performance enhancement experiments ----------------------------------------------


	/**
	 * An experiment to improve the performance of BLASimRelNBW by using 3 values 0,1,2 for the 
	   Duplicator's defense. 2 means success (true), 1 means weak fail (might succeed with higher lookehad),
	   and 0 means strong fail (even higher lookahead will not help because it cannot even do a transition with 
	   the required symbol.)
	   
	 * Compute the transitive closure of bounded lookahead direct forward simulation on/between two Buchi automata
	 * This is an underapproximation of direct forward trace inclusion.
	 * @param omega1, omega2: two Buchi automata. la: lookahead, must be >= 1
	 *
	 * @return A relation that underapproximates direct forward trace inclusion.

	 Experimental results: Can be up to 40% faster than BLASimRelNBW, 
	 but only for higher lookahead >= 4 and automata which are sparse 
	 or have low acceptance density, e.g., rd <= 1.6
	 Can be 10-15% slower for dense aut. and lower lookahead.
	 */

    public Set<Pair<FAState,FAState>> t_BLASimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2,int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		FAState[] states = all_states.toArray(new FAState[0]);

		boolean[][] W = new boolean[n_states][n_states];

		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		// Initialize result. This will shrink by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			if(isFinal[p] && !isFinal[q]) { W[p][q]=false; continue; }
			W[p][q]=true;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=false; // p can do action s, but q cannot
		    }

		boolean changed=true;
		while(changed){
		    // System.out.println("BLA sim. Outer iteration.");
		    changed = t_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,la);
		}
		}
		// Compute transitive closure
		close_transitive(W,n_states);

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(W[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean t_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n_states; p++)	
	    for(int q=0; q<n_states; q++){
		if(!W[p][q]) continue; // false remains false;
		attack[0]=p;
		if(t_BLA_attack(p,q,isFinal,n_states,n_symbols,post,post_len,W,la,attack,0)) { W[p][q]=false; changed=true; }
	    }
	return changed;
    }


private boolean t_BLA_attack(int p, int q, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if (depth==2*la) return (t_BLA_defense(p,q,isFinal,n_states,n_symbols,post,post_len,W,la,attack,0) < 2); // even weak fail is fail here 
    
    if (depth > 0){
	int r = t_BLA_defense(p,q,isFinal,n_states,n_symbols,post,post_len,W,(depth/2),attack,0); 
	if(r==2) return false; // defense successful even with lower lookahead; so attack fails
	if(r==0) return true; // defense strongly fails so that even higher lookahead would not help; so attack succeeds
	// if r==1 then it continues
    }

    // if deadlock for attacker then try the attack so far
    int successors=0;
    for(int s=0;s<n_symbols;s++) successors += post_len[s][attack[depth]];
    if(successors==0) {
	if(depth==0) return false;
	else return(t_BLA_defense(p,q,isFinal,n_states,n_symbols,post,post_len,W,(depth/2),attack,0) < 2); // even weak fail is fail here
    }
    
    for(int s=0;s<n_symbols;s++) 
	if(post_len[s][attack[depth]]>0){
	    for(int r=0; r<post_len[s][attack[depth]]; r++){
		attack[depth+1]=s;
		attack[depth+2]=post[s][attack[depth]][r];
		if(t_BLA_attack(p,q,isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2)) return(true);
	    }
	}
    return false;
}

private int t_BLA_defense(int p, int q, boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int la, int[] attack, int depth)
{
    if(isFinal[attack[depth]] && !isFinal[q]) return(0); // strong fail, acc condition violated
    if((depth >0) && W[attack[depth]][q]) return(2); // success
    if(depth==2*la){
	if(W[attack[depth]][q]) return(2); // success
	else return(1); // weak fail
    }
    int s=attack[depth+1];
    if(post_len[s][q]==0) return(0); // strong fail, cannot do required action
    int res=0; // initialize as worst case
    int curr=0;
    for(int r=0; r<post_len[s][q]; r++){
	curr = t_BLA_defense(p,post[s][q][r],isFinal,n_states,n_symbols,post,post_len,W,la,attack,depth+2);
	if(curr==2) return(2); // immediately report success
	if(curr > res) res=curr;
    }
    return(res); // this might be 0 or 1
}




//----------- Experiments with repeated transitive closure ------------------------------------------------------

	/**
	 * Compute the REPEATED transitive closure of bounded lookahead delayed forward simulation relation on/between two Buchi automata
	 * This is an underapproximation of n-pebble delayed forward simulation, and thus good for quotienting Buchi automata
	 * @param omega1, omega2: two Buchi automata. la: lookahead must be >=1.
	 *
	 * @return An underapproximation of n-pebble delayed forward simulation
	 */

public Set<Pair<FAState,FAState>> rep_BLADelayedSimRelNBW(FiniteAutomaton omega1,FiniteAutomaton omega2, int la) 
	{
		ArrayList<FAState> all_states=new ArrayList<FAState>();
		HashSet<String> alphabet=new HashSet<String>();

		all_states.addAll(omega1.states);
		alphabet.addAll(omega1.alphabet);

		if(omega2!=null){
			all_states.addAll(omega2.states);
			alphabet.addAll(omega2.alphabet);
		}

		int n_states = all_states.size();
		int n_symbols = alphabet.size();

		boolean[][] W = new boolean[n_states][n_states];
		boolean[][] suretrue = new boolean[n_states][n_states];

		FAState[] states = all_states.toArray(new FAState[0]);
		{
		ArrayList<String> symbols=new ArrayList<String>(alphabet);

		boolean[] isFinal = new boolean[n_states];
		for(int i=0;i<n_states;i++){			
			isFinal[i] = states[i].getowner().F.contains(states[i]);
		}
		
		int[][][] post = new int[n_symbols][n_states][];
		int[][] post_len = new int[n_symbols][n_states];
		
		for(int s=0;s<n_symbols;s++)
		{
			String a = symbols.get(s);
			for(int p=0; p<n_states; p++)
			    {
				//System.out.println("Delayed sim: Getting post: Iterating p: "+p+" of "+n_states+" s is "+s+" of "+n_symbols);
				post_len[s][p]=0;
				Set<FAState> next = states[p].getNext(a); 
				if (next != null){
				    post[s][p] = new int[states[p].getNext(a).size()];
				    for(int q=0; q<n_states; q++)
					{
					    if(next.contains(states[q]))
						{
						post[s][p][post_len[s][p]++] = q;
						}
					}
				}
			    }
		}

		boolean[][] avoid = new boolean[n_states][n_states];
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++) suretrue[p][q]=false;

		boolean rflag=true;
		while(rflag){
		// Initialize result W (winning for spolier). This will grow by least fixpoint iteration.
		for(int p=0; p<n_states; p++)
		    for(int q=0; q<n_states; q++){
			W[p][q]=false;
			for(int s=0;s<n_symbols;s++)
			    if(post_len[s][p]>0 && post_len[s][q]==0) W[p][q]=true; // p can do action s, but q cannot
		    }

		boolean changed=true;
		while(changed){
		    delayed_bla_get_avoid(avoid,isFinal,n_states,n_symbols,post,post_len,W,la);
		    changed=rep_delayed_BLA_refine(isFinal,n_states,n_symbols,post,post_len,W,avoid,la,suretrue);
		}
		
		// Invert to get duplicator winning states
		for(int p=0; p<n_states; p++)	
		    for(int q=0; q<n_states; q++) suretrue[p][q]=!W[p][q];

		// Compute transitive closure
		rflag = (close_transitive(suretrue,n_states) >0);
		}

		}

		// Create final result as set of pairs of states
		Set<Pair<FAState,FAState>> FSim2 = new TreeSet<Pair<FAState,FAState>>(new StatePairComparator());
		for(int p=0; p<n_states; p++)	
			for(int q=0; q<n_states; q++)
				if(suretrue[p][q]) // W is winning for spoiler here, so the result is the opposite.
					FSim2.add(new Pair<FAState, FAState>(states[p],states[q]));
		return FSim2;
	}


private boolean rep_delayed_BLA_refine(boolean[] isFinal, int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[][] avoid, int la, boolean[][] st)
    {
	int[] attack = new int[2*la+1];
	boolean changed=false;
	for(int p=0; p<n_states; p++)	
	    for(int q=0; q<n_states; q++){
		if(W[p][q]) continue; // true remains true; spoiler winning
		if(st[p][q]) continue; // these pairs may not be attacked. So W stays false here.
		attack[0]=p;
		if(delayed_BLA_attack(p,q,isFinal,n_states,n_symbols,post,post_len,W,avoid,la,attack,0)) { W[p][q]=true; changed=true; }
	    }
	return changed;
    }

// ----------------------------- Prerefine for delayed and acc_direct --------------------

// This functions determine the depth of the pre_prefine. Depends on the number of symbols and the desired lookahead.

private int depth_pre_refine(int la, int n_symbols)
{
    int magic = 140;  // 2^7 for depth 7, rounded up

    if(n_symbols <= 0) return 1;
    else if(n_symbols==1) return Math.min(la, 7);
    else if(n_symbols >= magic) return 1;
    else return Math.min(la,(int)(Math.log((double)magic)/Math.log((double)n_symbols)));
}

private int parallel_depth_pre_refine(int la, int n_symbols)
{
    int magic = 5000; // about 2^13 for depth 13

    if(n_symbols <= 0) return 1;
    else if(n_symbols==1) return Math.min(la, 13);
    else if(n_symbols >= magic) return 1;
    else return (int)(Math.log((double)magic)/Math.log((double)n_symbols));
}


private int delayed_pre_refine(int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, int depth)
{
    ArrayList<ArrayList<Set<int[]>>> cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> fulldo = new ArrayList<Set<int[]>>(depth);

    cando.add(0,new ArrayList<Set<int[]>>(n_states));
    // cando.get(0).ensureCapacity(n_states);
    for(int p=0; p<n_states; p++) cando.get(0).add(p,new HashSet<int[]>());
    fulldo.add(0,new HashSet<int[]>());
    
    for(int s=0; s<n_symbols; s++){
	int[] seq = new int[1];
	seq[0]=s;
	boolean flag=false;
	// fulldo.get(0).add(seq);
	for(int p=0; p<n_states; p++){
	    if(post_len[s][p] >0){
		(cando.get(0).get(p)).add(seq);
		if(!flag) { fulldo.get(0).add(seq); flag=true; }
	    }
	}
    }

    int res=0;
    for(int d=1; d<depth; d++){
	cando.add(d,new ArrayList<Set<int[]>>(n_states));
	for(int p=0; p<n_states; p++) cando.get(d).add(p, new HashSet<int[]>());
	fulldo.add(d, new HashSet<int[]>());
	Iterator<int[]> it = fulldo.get(d-1).iterator();
	while(it.hasNext()){
	    int[] oldseq = it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){
		    for(int r=0; r<post_len[s][p]; r++)
			if(cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    cando.get(d).get(p).add(seq);
			    if(!flag) { fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(W[p][q]) continue; // true stays true for delayed
		if(!cando.get(d).get(q).containsAll(cando.get(d).get(p))){
		    W[p][q]=true; // Spoiler wins
		    res++;
		}
	    }
    }

    return res;
}



// This is like pre_refine, except that it takes it into account whether the sequence ends in an accepting state.
// Uses up-to twice as much memory, but can remove more pairs (for the same depth).
// Unlike pre_refine, it is NOT correct to use for delayed/fair sim, but only for direct sim.

private int acc_pre_refine(int n_states, int n_symbols, int[][][] post, int[][] post_len, boolean[][] W, boolean[] isFinal, int depth)
{
    ArrayList<ArrayList<Set<int[]>>> cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> fulldo = new ArrayList<Set<int[]>>(depth);
    ArrayList<ArrayList<Set<int[]>>> acc_cando = new ArrayList<ArrayList<Set<int[]>>>(depth);
    ArrayList<Set<int[]>> acc_fulldo = new ArrayList<Set<int[]>>(depth);

    cando.add(0,new ArrayList<Set<int[]>>(n_states));
    acc_cando.add(0,new ArrayList<Set<int[]>>(n_states));
    // cando.get(0).ensureCapacity(n_states);
    for(int p=0; p<n_states; p++){
	cando.get(0).add(p,new HashSet<int[]>());
	acc_cando.get(0).add(p,new HashSet<int[]>());
    }
    fulldo.add(0,new HashSet<int[]>());
    acc_fulldo.add(0,new HashSet<int[]>());
    
    for(int s=0; s<n_symbols; s++){
	int[] seq = new int[1];
	seq[0]=s;
	boolean flag=false;
	boolean acc_flag=false;
	// fulldo.get(0).add(seq);
	for(int p=0; p<n_states; p++){
	    if(post_len[s][p] >0){
		(cando.get(0).get(p)).add(seq);
		if(!flag) { fulldo.get(0).add(seq); flag=true; }
	    }
	    for(int r=0; r<post_len[s][p]; r++)
		if(isFinal[post[s][p][r]]){
			(acc_cando.get(0).get(p)).add(seq);
			if(!acc_flag) { acc_fulldo.get(0).add(seq); acc_flag=true; }
		    }
	}
    }

    int res=0;
    for(int d=1; d<depth; d++){
	cando.add(d,new ArrayList<Set<int[]>>(n_states));
	acc_cando.add(d,new ArrayList<Set<int[]>>(n_states));
	for(int p=0; p<n_states; p++){
	    cando.get(d).add(p, new HashSet<int[]>());
	    acc_cando.get(d).add(p, new HashSet<int[]>());
	}
	fulldo.add(d, new HashSet<int[]>());
	acc_fulldo.add(d, new HashSet<int[]>());

	Iterator<int[]> it = fulldo.get(d-1).iterator();
	while(it.hasNext()){
	    int[] oldseq = it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){
		    for(int r=0; r<post_len[s][p]; r++)
			if(cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    cando.get(d).get(p).add(seq);
			    if(!flag) { fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	Iterator<int[]> acc_it = acc_fulldo.get(d-1).iterator();
	while(acc_it.hasNext()){
	    int[] oldseq = acc_it.next();
	    for(int s=0; s<n_symbols; s++){
		int[] seq = new int[d+1];
		for(int i=0; i<d; i++) seq[i]=oldseq[i];
		seq[d] = s;
		boolean flag=false;
		for(int p=0; p<n_states; p++){
		    for(int r=0; r<post_len[s][p]; r++)
			if(acc_cando.get(d-1).get(post[s][p][r]).contains(oldseq)){
			    acc_cando.get(d).get(p).add(seq);
			    if(!flag) { acc_fulldo.get(d).add(seq); flag=true; }
			    break;
			}
		}
	    }
	}

	for(int p=0; p<n_states; p++)
	    for(int q=0; q<n_states; q++){
		if(!W[p][q]) continue;
		if(!cando.get(d).get(q).containsAll(cando.get(d).get(p))){
		    W[p][q]=false;
		    res++;
		    continue;
		}
		if(!acc_cando.get(d).get(q).containsAll(acc_cando.get(d).get(p))){
		    W[p][q]=false;
		    res++;
		}
	    }
    }

    return res;
}


}

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

import java.util.Iterator;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;


public class SCC {
	int index=0;
	Stack<FAState> S=new Stack<FAState>();
	FiniteAutomaton fa;
	TreeMap<Integer,Integer> v_index=new TreeMap<Integer,Integer>();
	TreeMap<Integer,Integer> v_lowlink=new TreeMap<Integer,Integer>();
	TreeSet<FAState> OneSCC=new TreeSet<FAState>();

	public TreeSet<FAState> getResult(){
		return OneSCC;
	}
	
	public SCC(FiniteAutomaton fa){
		this.fa=fa;
		Iterator<FAState> st_it=fa.states.iterator();
		while(st_it.hasNext()){
			FAState st=st_it.next();
			if(!v_index.containsKey(st.id)){
				tarjan(st, false);
			}
		}
	}
	public SCC(FiniteAutomaton fa, boolean node){
		this.fa=fa;
		Iterator<FAState> st_it=fa.states.iterator();
		while(st_it.hasNext()){
			FAState st=st_it.next();
			if(!v_index.containsKey(st.id)){
				tarjan(st, node);
			}
		}
	}

	
	void tarjan(FAState v, boolean node){
		v_index.put(v.id, index);
		v_lowlink.put(v.id, index);
		index++;
		S.push(v);
		Iterator<String> next_it=v.nextIt();
		while(next_it.hasNext()){
			String next=next_it.next();
			Iterator<FAState> st_it=v.getNext(next).iterator();
			while(st_it.hasNext()){
				FAState v_prime=st_it.next();
				if(!v_index.containsKey(v_prime.id)){
					tarjan(v_prime, node);
					v_lowlink.put(v.id,	Math.min(v_lowlink.get(v.id), v_lowlink.get(v_prime.id)));
				}else if(S.contains(v_prime)){
					v_lowlink.put(v.id,	Math.min(v_lowlink.get(v.id), v_index.get(v_prime.id)));
				}
			}
		}
		if(v_lowlink.get(v.id).intValue()==v_index.get(v.id).intValue()){
			TreeSet<FAState> SCC=new TreeSet<FAState>();
			while(!S.empty()){
				FAState t=S.pop();
				SCC.add(t);
				if(t.id==v.id)
					break;
			}
			if(SCC.size()==1&&node){
				FAState st=SCC.iterator().next();
				if(!(st.getNext()!=null && st.getNext().contains(st))){
					return;
				}
			}
			Iterator<FAState> SCC_it=SCC.iterator();
			while(SCC_it.hasNext()){
				FAState st=SCC_it.next();
				if(!node){
					Set<FAState> states=st.getNext("1");
					if(states!=null){
						states.retainAll(SCC);
						if(states.size()!=0){//is 1-SCC
							Iterator<FAState> SCC_it2=SCC.iterator();
							while(SCC_it2.hasNext()){
								OneSCC.add(SCC_it2.next());
							}
							break;
						}
					}
				}else{
					if(fa.F.contains(st)){//is 1-SCC
						Iterator<FAState> SCC_it2=SCC.iterator();
						while(SCC_it2.hasNext()){
							OneSCC.add(SCC_it2.next());
						}
						break;
					}
				}
			}
		}
	}
	
/*
procedure tarjan(v)
  index = index + 1
  S.push(v)                       // Push v on the stack
  forall (v, v') in E do          // Consider successors of v
    if (v'.index is undefined)    // Was successor v' visited?
        tarjan(v')                // Recurse
        v.lowlink = min(v.lowlink, v'.lowlink)
    else if (v' is in S)          // Was successor v' in stack S? 
        v.lowlink = min(v.lowlink, v'.index)
  if (v.lowlink == v.index)       // Is v the root of an SCC?
    print "SCC:"
    repeat
      v' = S.pop
      print v'
    until (v' == v)

*/
	
}

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


import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FiniteAutomaton;

public class FAState implements Comparable<FAState>{
	TreeMap<String,TreeSet<FAState>> next;
	TreeMap<String,TreeSet<FAState>> pre;
	public int id;
	private FiniteAutomaton owner;
	
	public FAState(int i, FiniteAutomaton o){
		id=i;
		next=new TreeMap<String,TreeSet<FAState>>();
		pre=new TreeMap<String,TreeSet<FAState>>();
		owner=o;
	}
	public Iterator<String> nextIt(){
		return next.keySet().iterator();
	}
	public Iterator<String> preIt(){	
		return pre.keySet().iterator();
	}
	public String toString(){
		return "S"+id+"_"+owner.name;
	}
	public int getID(){
		return id;
	}
	public Set<FAState> getNext(){
		Set<FAState> result=new TreeSet<FAState>();
		Iterator<String> key_it=next.keySet().iterator();
		while(key_it.hasNext()){
			String key=key_it.next();
			result.addAll(next.get(key));
		}
		return result;
	}
	public Set<FAState> getPre(){
		Set<FAState> result=new TreeSet<FAState>();
		Iterator<String> key_it=pre.keySet().iterator();
		while(key_it.hasNext()){
			String key=key_it.next();
			result.addAll(pre.get(key));
		}
		return result;
	}

	public FiniteAutomaton getowner(){
	    return owner;
	}
	
	public Set<FAState> getNext(String a){
		return next.get(a);
	}
	public Set<FAState> getPre(String a){
		return pre.get(a);
	}
	public void addNext(String a, FAState b, FiniteAutomaton auto){
		if(!next.containsKey(a)){
			TreeSet<FAState> S = new TreeSet<FAState>();
			S.add(b);
			next.put(a,S);
		}else
			next.get(a).add(b);
	}

	/** 
	 * @param s state
	 * @return if the set of out-going transitions of this state covers that of s 
	 */
	public boolean fw_covers(FAState s)
	{
		Iterator<String> it = s.nextIt();
		while(it.hasNext())
		{
			String ss = it.next();
			if(!next.containsKey(ss))
				return false;
		}
		return true;
	}

	/** 
	 * @param s state
	 * @return if the set of incoming transitions of this state covers that of s 
	 */
	public boolean bw_covers(FAState s)
	{
		Iterator<String> it = s.preIt();
		while(it.hasNext())
		{
			String ss = it.next();
			if(!pre.containsKey(ss))
				return false;
		}
		return true;
	}
	
	public void addPre(String a, FAState n){
		if(pre.get(a)==null){
			pre.put(a, new TreeSet<FAState>());
		}
		pre.get(a).add(n);
	}
	public int compareTo(FAState o) {
		if(owner!=((FAState)o).owner)
			return owner.hashCode()-((FAState)o).owner.hashCode();
		return o.getID()-id;
	}
	public boolean equals(Object o) {
		return ((FAState)o).getID()==id &&owner==((FAState)o).owner;
	}

}

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

package datastructure;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.TreeSet;

import algorithms.Options;

public class Graph implements Comparable<Graph>, Cloneable, Iterable<Arc>{
	private TreeMap<Integer, TreeSet<Arc>> data2;
	int size=0;
	
	public boolean containsLeftState(int st){
		return data2.containsKey(st);
	}
	public Graph(){
		data2=new TreeMap<Integer, TreeSet<Arc>>();
		size=0;
	}
	public Iterator<Integer> leftStateIt(){
		return data2.keySet().iterator();
	}
	public Iterator<Arc> iterator(int x){
		if(data2.containsKey(x))
			return data2.get(x).iterator();
		else 
			return new TreeSet<Arc>().iterator();
	}
	
	public boolean addAll(Graph h){
		boolean success=true;
		Iterator<Integer> leftSt_it=h.leftStateIt();
		while(leftSt_it.hasNext()){
			int leftSt=leftSt_it.next();
			if(!data2.containsKey(leftSt)){
				data2.put(leftSt, new TreeSet<Arc>());
			}
			int preSize=data2.get(leftSt).size();
			success=success&&data2.get(leftSt).addAll(h.data2.get(leftSt));
			size+=(data2.get(leftSt).size()-preSize);
		}
		return success;
	}
	public void add(Arc a){
		if(!data2.containsKey(a.getFrom())){
			data2.put(a.getFrom(), new TreeSet<Arc>());
		}
		if(!data2.get(a.getFrom()).contains(a)){
			data2.get(a.getFrom()).add(a);
			size++;
		}
	}
	public boolean contains(Arc a){
		if(data2.containsKey(a.getFrom())){
			return data2.get(a.getFrom()).contains(a);
		}else
			return false;
	}
	public void remove(Arc a) {
		if(data2.containsKey(a.getFrom())){
			if(data2.get(a.getFrom()).contains(a)){
				data2.get(a.getFrom()).remove(a);
				size--;
				if(data2.get(a.getFrom()).size()==0)
					data2.remove(a.getFrom());
			}
		}
	}
	
	public int size() {
		return size;
	}
	public void clear() {
		data2.clear();
		size=0;
	}
	public String toString(){
		if(!Options.debug)
		return "";
		return data2.toString();
	}
	
	public Graph clone(){
		Graph dup=new Graph();
		Iterator<Integer> curInt_it=data2.keySet().iterator();
		while(curInt_it.hasNext()){
			int curInt=curInt_it.next();
			Iterator<Arc> cur_it=data2.get(curInt).iterator();
			while(cur_it.hasNext()){
				Arc arc=cur_it.next();
				Arc dupArc=new Arc(arc.getFrom(),arc.getLabel(),arc.getTo());
				dupArc.L=arc.L;
				dup.add(dupArc);
			}
		}
		return dup;
	}
	
	public int compareTo(Graph oth) {

		if(size!=oth.size){
			return size-oth.size;
		}else if(data2.size()!=oth.data2.size()){
			return data2.size()-oth.data2.size();
		}else if(data2.keySet().size()!=oth.data2.keySet().size()){
			return data2.keySet().size()-oth.data2.keySet().size();
		}else{
			Iterator<Integer> curInt_it=data2.keySet().iterator();
			Iterator<Integer> othInt_it=oth.data2.keySet().iterator();
			while(curInt_it.hasNext()){
				int curInt=curInt_it.next();
				int othInt=othInt_it.next();
				if(curInt!=othInt){
					return curInt-othInt;
				}else{
					if(data2.get(curInt).size()!=oth.data2.get(curInt).size())
						return data2.get(curInt).size()-oth.data2.get(curInt).size();
					Iterator<Arc> cur_it=data2.get(curInt).iterator();
					Iterator<Arc> oth_it=oth.data2.get(curInt).iterator();
					while(cur_it.hasNext()){
						Arc curArc=cur_it.next();
						Arc othArc=oth_it.next();
						int larger=curArc.compareTo(othArc);
						if(larger!=0){
							return larger;
						}
					}
				}
			}
			return 0;
		}
	}
	@Override
	public Iterator<Arc> iterator() {
		System.out.println("Iterator is called!");
		System.exit(0);
		return null;
	}
}

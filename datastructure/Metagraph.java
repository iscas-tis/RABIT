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

import java.util.TreeSet;

public class Metagraph implements Comparable<Metagraph>{
	public Metagraph(Pair<TreeSet<Arc>, TreeSet<Arc>> e){
		left=e.getLeft();
		right=e.getRight();
	}
	public Metagraph(TreeSet<Arc> left, TreeSet<Arc> right){
		this.left=left;
		this.right=right;
	}
	public Metagraph(TreeSet<Arc> left, TreeSet<Arc> right, String rpstring){
		this.rpstring=rpstring;
		this.left=left;
		this.right=right;
	}
	
	TreeSet<Arc> left;
	TreeSet<Arc> right;
	public TreeSet<Arc> getLeft(){
		return left;
	}
	public TreeSet<Arc> getRight(){
		return right;
	}
	public String rpstring;
	public Pair<TreeSet<Arc>, TreeSet<Arc>> getGraph(){return new Pair<TreeSet<Arc>, TreeSet<Arc>>(left,right);};

	private int compare(TreeSet<Arc> arg0, TreeSet<Arc> arg1) {
		return arg0.toString().compareTo(arg1.toString());
	}

	public String toString() {
		return getGraph().toString();
	}
	
	public int compareTo(Metagraph other) {
		if(this.getLeft().toString().compareTo(other.getLeft().toString())==0)
			return compare(this.getRight(),other.getRight());
		else
			return this.getLeft().toString().compareTo(other.getLeft().toString());
	}
}

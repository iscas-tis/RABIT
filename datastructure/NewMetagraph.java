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

public class NewMetagraph implements Comparable<NewMetagraph>{
	public NewMetagraph(Pair<Graph, Graph> e){
		left=e.getLeft();
		right=e.getRight();
	}
	public NewMetagraph(Graph left, Graph right){
		this.left=left;
		this.right=right;
	}
	public NewMetagraph(Graph left, Graph right, String rpstring){
		this.rpstring=rpstring;
		this.left=left;
		this.right=right;
	}
	
	Graph left;
	Graph right;
	public Graph getLeft(){
		return left;
	}
	public Graph getRight(){
		return right;
	}
	public String rpstring;
	public Pair<Graph, Graph> getGraph(){return new Pair<Graph, Graph>(left,right);};

	private int compare(Graph arg0, Graph arg1) {
		return arg0.compareTo(arg1);
	}

	public String toString() {
		return getGraph().toString();
	}
	
	public int compareTo(NewMetagraph other) {
		if(this.getLeft().compareTo(other.getLeft())==0)
			return compare(this.getRight(),other.getRight());
		else
			return this.getLeft().compareTo(other.getLeft());
	}
}

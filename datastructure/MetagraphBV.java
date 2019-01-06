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

import java.util.BitSet;

public class MetagraphBV implements Comparable<MetagraphBV>{
    public MetagraphBV(Pair<BitSet, BitSet> e, String rpstring){
		this.left=e.getLeft();
		this.right=e.getRight();
		this.rpstring=rpstring;
	}
    public MetagraphBV(BitSet left, BitSet right, String rpstring){
		this.left=left;
		this.right=right;
		this.rpstring=rpstring;
	}
	BitSet left;
	BitSet right;
	public BitSet getLeft(){
		return left;
	}
	public BitSet getRight(){
		return right;
	}
	public String rpstring;
	public Pair<BitSet, BitSet> getGraph(){return new Pair<BitSet, BitSet>(left,right);};

	public String toString() {
		return getGraph().toString();
	}
	
	public int compareTo(MetagraphBV other) {
		if(this.getLeft().equals(other.getLeft()))
			return this.getRight().toString().compareTo(other.getRight().toString());
		else
			return this.getLeft().toString().compareTo(other.getLeft().toString());
	}
}

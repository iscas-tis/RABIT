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

public class Arc implements Comparable<Arc>{
	private int e1, e2;
	private boolean l;
	public boolean L=false, R=false;
	
	
	public Arc(int e1, boolean l, int e2){
		this.e1 = e1;
		this.e2 = e2;
		this.l=l;
	}

	public int getFrom() {
		return this.e1;
	}

	public int getTo() {
		return this.e2;
	}

	public boolean getLabel() {
		return this.l;
	}

	@Override
	public String toString() {
		String label="N";
		if(L) label="L";
		return "<" + e1 + ", " + l + ", " + e2 +"> ("+label+")";
	}

	public int compareTo(Arc other) {
		if(other.e1!=e1){
			return other.e1-e1;
		}else if(other.e2!=e2){
			return other.e2-e2;
		}else if(other.l!=l){
			if(other.l)	return 1;
			else return -1;
		}else if(L==true && other.L==false){//consider the case where we have two metagraph g, h g.left={0=[<0, true, 0> (N)]} and h.left={0=[<0, true, 0> (L)]}
			return -1;
		}else if(L==false && other.L==true){//consider the case where we have two metagraph g, h g.left={0=[<0, true, 0> (N)]} and h.left={0=[<0, true, 0> (L)]}
			return 1;
		}else{
			return 0;
		}
	}
}

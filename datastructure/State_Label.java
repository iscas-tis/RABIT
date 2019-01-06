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

import automata.FAState;

public class State_Label implements Comparable<State_Label>{

	private FAState st;
	private String l;

	public State_Label(FAState st, String l){
		this.st = st;
		this.l = l;
	}

	public FAState getState() {
		return st;
	}

	public String getLabel() {
		return this.l;
	}

	@Override
	public String toString() {
		return "<" + st + ", " + l+ ">";
	}

	public int compareTo(State_Label other) {
		if(other.st.compareTo(st)!=0){
			return other.st.compareTo(st);
		}else if(other.l.compareTo(l)!=0){
			return other.l.compareTo(l);
		}else{
			return 0;
		}
	}
	
	@Override
	public int hashCode(){
		return st.hashCode()+l.hashCode();
	}
}

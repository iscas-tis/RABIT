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

public class Pair<E1, E2> {

	private E1 e1 = null;

	private E2 e2 = null;

	public Pair(E1 e1, E2 e2) {
		this.e1 = e1;
		this.e2 = e2;
	}

	public E1 getLeft() {
		return this.e1;
	}

	public E2 getRight() {
		return this.e2;
	}

	@Override
	public String toString() {
		String str1 = this.e1 == null ? "null" : this.e1.toString();
		String str2 = this.e2 == null ? "null" : this.e2.toString();
		return "(" + str1 + ", " + str2 + ")";
	}

	@Override
	public int hashCode() {
		return this.e1.hashCode() ^ this.e2.hashCode() * 29;
	}

	public boolean equals(Pair<E1, E2> o) {
		try {
			Pair<E1, E2> temp = o;
			return this.e1.equals(temp.getLeft())
					&& this.e2.equals(temp.getRight());
		} catch (ClassCastException e) {
			return false;
		}
	}
}

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

package comparator;


import java.util.TreeSet;

import java.util.Comparator;

import datastructure.Arc;
import datastructure.Pair;




public class MetaGraphComparator implements Comparator<Pair<TreeSet<Arc>,TreeSet<Arc>>> {
	public int compare(TreeSet<Arc> arg0, TreeSet<Arc> arg1) {
			return arg0.toString().compareTo(arg1.toString());
	}

	public int compare(Pair<TreeSet<Arc>, TreeSet<Arc>> arg0,
			Pair<TreeSet<Arc>, TreeSet<Arc>> arg1) {
		if(arg0.getLeft().toString().compareTo(arg1.getLeft().toString())==0)
			return compare(arg0.getRight(),arg1.getRight());
		else
			return arg0.getLeft().toString().compareTo(arg1.getLeft().toString());
	}
}
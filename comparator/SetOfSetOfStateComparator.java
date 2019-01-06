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


import java.util.Comparator;
import java.util.Iterator;
import java.util.SortedSet;

import automata.FAState;





public class SetOfSetOfStateComparator implements
		Comparator<SortedSet<FAState>> {

	public int compare(SortedSet<FAState> o1, SortedSet<FAState> o2) {
		if(o1.size()>o2.size()){
			return 1;
		}else if(o1.size()<o2.size()){
			return -1;
		}else{
			Iterator<FAState> it1=o1.iterator();
			Iterator<FAState> it2=o2.iterator();
			while(it1.hasNext()){
				FAState s1=it1.next();
				FAState s2=it2.next();
				if(s1.compareTo(s2)<0)
					return -1;
				else if(s1.compareTo(s2)>0)
					return 1;
			}
			return 0;
		}
	}
}
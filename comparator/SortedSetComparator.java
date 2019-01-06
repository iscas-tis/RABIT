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





public class SortedSetComparator implements Comparator<SortedSet<FAState>> {

	public int compare(SortedSet<FAState> s1, SortedSet<FAState> s2){
		if(s1.size()>s2.size()){
			return 1;
		}else if(s1.size()<s2.size()){
			return -1;
		}else{
			Iterator<FAState> iter1 = s1.iterator();
			Iterator<FAState> iter2 = s2.iterator();
			
			while(iter1.hasNext()){
				FAState st1=iter1.next();
				FAState st2=iter2.next();
				if(st1.compareTo(st2)>0){
					return 1;
				}else if(st1.compareTo(st2)<0){
					return -1;
				}
			}
			return 0;
		}
	}

	
}

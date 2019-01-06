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


import java.util.BitSet;
import java.util.TreeSet;

import java.util.Comparator;

import datastructure.Arc;
import datastructure.Pair;




public class MetaGraphBitVectorComparator implements Comparator<Pair<BitSet,BitSet>> {
	public int compare(Pair<BitSet, BitSet> arg0, Pair<BitSet, BitSet> arg1) {
		if(arg0.getLeft().size()>arg1.getLeft().size()){
			return 1;
		}else if(arg0.getLeft().size()<arg1.getLeft().size()){
			return -1;
		}else if(arg0.getRight().size()>arg1.getRight().size()){
			return 1;
		}else if(arg0.getRight().size()<arg1.getRight().size()){
			return -1;
		}else{
			for(int i=0;i<arg0.getLeft().size();i++){
				if(arg0.getLeft().get(i)&&!arg0.getLeft().get(i)){
					return 1;
				}else if(!arg0.getLeft().get(i)&&arg0.getLeft().get(i)){
					return -1;
				}
			}
			for(int i=0;i<arg0.getRight().size();i++){
				if(arg0.getRight().get(i)&&!arg0.getRight().get(i)){
					return 1;
				}else if(!arg0.getRight().get(i)&&arg0.getRight().get(i)){
					return -1;
				}
			}
		}
		
		return 0;
	}
}
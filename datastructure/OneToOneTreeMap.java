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

import java.util.Map;
import java.util.TreeMap;

public class OneToOneTreeMap<K,V> implements OneToOneMap<K,V> {

	  private Map<K,V> mapKey;
	  private Map<V,K> mapValue;
	  
	  public OneToOneTreeMap(){
	    mapKey = new TreeMap<K,V>();
	    mapValue = new TreeMap<V,K>();
	  }
	  
	  public void put(K key, V value) {
		  if(mapKey.containsKey(key)){
			  mapKey.remove(key);
		  }
		  if(mapValue.containsKey(value)){
			  mapValue.remove(value);
		  }
		  mapKey.put(key, value);
		  mapValue.put(value, key);
	  }

	  public void removeKey(K key) {
	       V value = mapKey.remove(key);
	       mapValue.remove(value);
	  }

	  public void removeValue(V value) {
	       K key = mapValue.remove(value);
	       mapKey.remove(key);
	  }

	  public boolean containsValue(V value){
		  return mapValue.containsKey(value);
	  }
	  public boolean containsKey(K key){
		  return mapKey.containsKey(key);
	  }
	  public V getValue(K key){
	    return mapKey.get(key);
	  }

	  public K getKey(V value){
	    return mapValue.get(value);
	  }
}

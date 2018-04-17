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

package mainfiles;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.management.*;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import automata.FAState;
import automata.FiniteAutomaton;

/**
 * 
 * @author Richard Mayr
 * 
 */
public class toTimbuk {
	public static void main(String[] args) {	
		Random r = new Random();
		if(args.length<1){
		    System.out.println("This tool converts the .ba word-automata format into (a fragment of) the .timbuk tree-automata format. It does not exactly preserve the language (the empty word is removed and a special accept symbol added at the end), but it does preserve language inclusion between any two automata so converted.");
			System.out.println("Usage: java -jar toTimbuk.jar file.ba");
			System.out.println("Output: file.ba.timbuk");
		}else{
			FiniteAutomaton ba = new FiniteAutomaton(args[0]);
			ba.saveAutomatonTimbuk2(args[0]+".timbuk");
		}
	}
			
}

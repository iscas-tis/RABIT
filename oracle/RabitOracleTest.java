/* Written by Yong Li                                                     */
/* Copyright (c) 2016                  	                                  */
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

package oracle;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.BeforeClass;
import org.junit.Test;

import automata.FiniteAutomaton;

public class RabitOracleTest {

	private static FiniteAutomaton aut1 ;
	private static FiniteAutomaton aut2 ;
	private static FiniteAutomaton aut3 , aut4, aut5, aut6, aut7;
	static List<String> prefix = new ArrayList<>();
	static List<String> suffix = new ArrayList<>();
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		
		String dir = "C:/Users/liyong/workspace/rabittest/";
		aut1 = new FiniteAutomaton(dir + "a.ba");
		aut2 = new FiniteAutomaton(dir + "ab.ba");
		aut3 = new FiniteAutomaton(dir + "aab.ba");
		aut4 = new FiniteAutomaton(dir + "bug8.ba");
		aut5 = new FiniteAutomaton(dir + "bugrecur.ba");
		aut6 = new FiniteAutomaton(dir + "testmem.ba");
		aut7 = new FiniteAutomaton("C:/Users/liyong/workspace/jalf/jalf/bug.ba");
		prefix.add("a");
		suffix.add("a");
	}

	@Test
	public void testIsAccepted1() {
		RabitOracle rabit = new RabitOracle(aut1);
		assertEquals(true, rabit.isAccepted(prefix, suffix));
		rabit = new RabitOracle(aut2);
		assertEquals(true, rabit.isAccepted(prefix, suffix));
		rabit = new RabitOracle(aut3);
		assertEquals(true, rabit.isAccepted(prefix, suffix));
		List<String> pre = new ArrayList<>();
		List<String> suf = new ArrayList<>();
		pre.add("a");
		pre.add("b");
		suf.add("b");
		assertEquals(true, rabit.isAccepted(pre, suf));
		pre.add("b");
		assertEquals(true, rabit.isAccepted(pre, suf));
		pre.add("a");
		assertEquals(false, rabit.isAccepted(pre, suf));
		rabit = new RabitOracle(aut4);
		pre.clear();
		suf.clear();
		suf.add("b");
		suf.add("a");
		assertEquals(false, rabit.isAccepted(pre, suf));
	}
	
	@Test
	public void testIsAccepted2() {
		List<String> pre = new ArrayList<>();
		List<String> suf = new ArrayList<>();
		RabitOracle rabit = new RabitOracle(aut2);
		pre.add("a");
		assertEquals(false, rabit.isAccepted(pre, suf));
		pre.add("a");
		assertEquals(false, rabit.isAccepted(pre, suf));
		pre.add("b");
		assertEquals(false, rabit.isAccepted(pre, suf));
	}
	
	@Test
	public void testIsAccepted3() {
		List<String> pre = new ArrayList<>();
		List<String> suf = new ArrayList<>();
		RabitOracle rabit = new RabitOracle(aut5);
		pre.add("a");
		suf.add("b");
		suf.add("b");
		suf.add("b");
		suf.add("b");
		suf.add("a");
		assertEquals(true, rabit.isAccepted(pre, suf));
	}
	
	@Test
	public void testIsAccepted4() {
		List<String> pre = new ArrayList<>();
		List<String> suf = new ArrayList<>();
		RabitOracle rabit = new RabitOracle(aut6);
		pre.add("b");
		suf.add("a");
		suf.add("b");
		suf.add("b");
		suf.add("a");

		assertEquals(true, rabit.isAccepted(pre, suf));
	}
	
	@Test
	public void testIsAccepted5() {
		List<String> pre = new ArrayList<>();
		List<String> suf = new ArrayList<>();
		RabitOracle rabit = new RabitOracle(aut7);
		pre.clear();
		pre.add("a");
		pre.add("c");
		pre.add("a");
		pre.add("b");
		suf.clear();
		suf.add("a");
		suf.add("b");

		assertEquals(true, rabit.isAccepted(pre, suf));
	}
	
	@Test
	public void testEqualBuechi1() {
		RabitOracle rabit = new RabitOracle(aut2);
		assertEquals(false, rabit.isEqualBuechi(aut1).isEqual);
	}
	
	@Test
	public void testEqualBuechi2() {
		RabitOracle rabit = new RabitOracle(aut2);
		assertEquals(false, rabit.isEqualBuechi(aut1).isEqual);
		assertEquals(false, rabit.isEqualBuechi(aut3).isEqual);
	}
	
	@Test
	public void testEqualBuechi3() {
		RabitOracle rabit = new RabitOracle(aut1);
		assertEquals(false, rabit.isEqualBuechi(aut2).isEqual);
		assertEquals(false, rabit.isEqualBuechi(aut3).isEqual);
	}
	
	@Test
	public void testEqualBuechi4() {
		RabitOracle rabit = new RabitOracle(aut3);
		assertEquals(false, rabit.isEqualBuechi(aut1).isEqual);
		assertEquals(false, rabit.isEqualBuechi(aut2).isEqual);
	}

}

/* Written by Yu-Fang Chen, Richard Mayr, and Chih-Duo Hong               */
/* Copyright (c) 2010-2012                                                        */
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

import java.lang.management.*;

/*
import java.util.Random;
import java.util.TreeMap;
import java.util.Iterator;

import java.util.Arrays;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
*/

import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import datastructure.Pair;

import automata.FAState;
import automata.FiniteAutomaton;
import automata.FAState;
import automata.FiniteAutomaton;
import algorithms.Minimization;
import algorithms.Options;
import algorithms.ParallelMinimization;
import algorithms.Simulation;
import algorithms.ParallelSimulation;


/**
 * 
 * @author Richard Mayr
 * 
 */
public class Quobug {

    public static void main(String[] args) {

      Options.debug = false;
      Options.fast=true;
      Options.backward=true;
      Options.rd=true;
      Options.fplus=true;
      Options.SFS=true;
      Options.qr=true;
      Options.C1=true;
      Options.EB=false; // difference to fast. EB must be false to report counterexamples
      Options.CPT=true;
      Options.superpruning=true;
      Options.delayed=true;
      Options.blamin=true;
      Options.blasub=true;
      Options.transient_pruning=true;
      Options.jumpsim_quotienting=true;
      Options.verbose=false; // set verbose to true to report counterexample
        
    FiniteAutomaton system = new FiniteAutomaton("/home/liyong/workspace-neon/roll-library/src/main/resources/inclusion/system.ba");
    FiniteAutomaton spec = new FiniteAutomaton("/home/liyong/workspace-neon/roll-library/src/main/resources/inclusion/spec.ba");

    Simulation sim = new Simulation();
    Minimization min = new Minimization();

    Set<Pair<FAState, FAState>> frel;
    
    frel = sim.ForwardSimRelNBW(system, spec);
    if(frel.contains(new datastructure.Pair<FAState, FAState>(system.getInitialState(), spec.getInitialState())))
        System.out.println("Included");;
    system = min.quotient(system, frel);
        spec = min.quotient(spec, frel); 

    system.saveAutomaton("/home/liyong/workspace-neon/roll-library/src/main/resources/inclusion/new_system.ba");

    }
}
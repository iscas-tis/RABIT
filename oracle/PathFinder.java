package oracle;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.Pair;

// use dijskstra 
class PathFinder {
	private int[] dist ;
	private FAState[] prev ;
	private String[] labels;
	private PriorityQueue Q;
	private FiniteAutomaton automaton;
	private FAState source;
	private FAState target;
	
	public PathFinder(FiniteAutomaton aut) {
		dist = new int[aut.states.size()];
		prev = new FAState[aut.states.size()];
		labels = new String[aut.states.size()];
		automaton = aut;
	}
	
	public void setSourceState(FAState s) {
		source = s;
	}
	
	public void setTargetState(FAState t) {
		target = t;
	}
	
	
	public Pair<List<FAState>, List<String>> findCycle() {
		assert source.id == target.id;
		// find a shortest path to itself. be sure it exists
		List<FAState> run = new LinkedList<>();
		List<String> word = new LinkedList<>();
		
		Iterator<String> pre_it = source.preIt();
		int dis = Integer.MAX_VALUE;
		setSourceState(source);
		while(pre_it.hasNext()) {
			String label = pre_it.next();
			Iterator<FAState> st_it = source.getPre(label).iterator();
			while(st_it.hasNext()) {
				FAState pre = st_it.next();
				if(pre.id == source.id) {
					// self loop
					run = new LinkedList<>();
					word = new LinkedList<>();
					run.add(source);
					run.add(source);
					word.add(label);
					return new Pair<>(run, word);
				}
				// pre != source
				setTargetState(pre);
				findPath();
				if(dist[pre.id] < dis) { // can reach
					Pair<List<FAState>, List<String>> result = getPath();
					run = result.getLeft();
					run.add(source);
					word = result.getRight();
					word.add(label);
				}
			}
		}
		
		return new Pair<>(run, word);
	}
	
	public void findPath() {
		findPath(source, target);
	}
	
	// two state should not be the same
	private void findPath(FAState s, FAState t) {
		dist[s.id] = 0;
		Q = new PriorityQueue(automaton.states.size()
				, new ComparatorFAState());
		FAState[] map = new FAState[automaton.states.size()];
		for(FAState state : automaton.states) {
			if(s.id != state.id) {
				dist[state.id] = Integer.MAX_VALUE;
				prev[state.id] = null;
				labels[state.id] = null;
			}
			Q.add(state.id);
			map[state.id] = state;
		}
		
		boolean[] visited = new boolean[automaton.states.size()];
		
		while(! Q.isEmpty()) {
			int u = Q.remove();
			if(visited[u]) continue;
			if(t.id == u || dist[u] == Integer.MAX_VALUE) { 
				// already found shortest path or no reachable state
				return ;
			}
			visited[u] = true;
			FAState uState = map[u];
			Iterator<String> next_it = uState.nextIt();
			while(next_it.hasNext()){
				String next = next_it.next();
				Iterator<FAState> st_it = uState.getNext(next).iterator();
				while(st_it.hasNext()) {
					FAState v = st_it.next();
					int dis = dist[u] + 1;
					if(dist[v.id] > dis && ! visited[v.id]) {//value become smaller
						dist[v.id] = dis;
						prev[v.id] = uState;
						labels[v.id] = next;
						Q.bubbleUpValue(v.id);
					}
				}
			}
		}
	}
	
	public Pair<List<FAState>, List<String>> getPath() {
		
		if(dist[target.id] == Integer.MAX_VALUE) return null;
		
		LinkedList<FAState> run = new LinkedList<>();
		LinkedList<String> word = new LinkedList<>();
		FAState p = target;
		
		while(p.id != source.id) {
			run.addFirst(p);
			word.addFirst(labels[p.id]);
			p = prev[p.id];
		}
		
		run.addFirst(source);
		
		return new Pair<>(run, word);
	}
	
	
	public boolean checkPath(FAState s, FAState t) {
		setSourceState(s);
		setTargetState(t);
		findPath();
		Pair<List<FAState>, List<String>> result = getPath();
		if(result == null) return true;
		List<FAState> run = result.getLeft();
		List<String> word = result.getRight();
		// check following results
		FAState p = run.get(0);
		for(int i = 0; i < word.size(); i ++) {
			Set<FAState> succs = p.getNext(word.get(i));
            boolean flag = false;
			for(FAState succ : succs) {
				if(succ.id == run.get(i + 1).id) {
					flag = true;
				}
			}
			if(! flag) return false;
			p = run.get(i + 1);
		}
		return true;
	}
	
	
	private class ComparatorFAState implements Comparator<Integer> {
		public ComparatorFAState() {
		}
		@Override
		public int compare(Integer a, Integer b) {
			if(dist[a] == Integer.MAX_VALUE) return 1;
			if(dist[b] == Integer.MAX_VALUE) return -1;
			
			if(dist[a] < dist[b]) {
				return -1;
			}
			if(dist[a] > dist[b]) {
				return 1;
			}
			return 0;
		}
		
	}
	
	
	public static void main(String[] args) {
		FiniteAutomaton aut = new FiniteAutomaton();
		FAState q0 = aut.createState();
		FAState q1 = aut.createState();
		FAState q2 = aut.createState();
		FAState q3 = aut.createState();
		FAState q4 = aut.createState();
		FAState q5 = aut.createState();
		FAState q6 = aut.createState();
		
		aut.setInitialState(q0);
		aut.F.add(q4);
		aut.F.add(q2);
		
		aut.addTransition(q0, q0, "a");
		aut.addTransition(q0, q1, "a");
		aut.addTransition(q0, q2, "a");
		aut.addTransition(q0, q3, "b");
		
		aut.addTransition(q1, q1, "a");
		aut.addTransition(q1, q2, "a");
		
		aut.addTransition(q2, q1, "a");
		
		aut.addTransition(q3, q3, "a");
		aut.addTransition(q3, q3, "b");
		aut.addTransition(q3, q4, "b");
		aut.addTransition(q3, q5, "a");
		aut.addTransition(q3, q6, "b");
		
		aut.addTransition(q4, q5, "a");
		aut.addTransition(q4, q6, "b");
		
		aut.addTransition(q5, q4, "b");
		aut.addTransition(q5, q5, "a");
		aut.addTransition(q5, q6, "b");
		
		aut.addTransition(q6, q4, "b");
		aut.addTransition(q6, q5, "a");
		aut.addTransition(q6, q6, "b");
		
		PathFinder path = new PathFinder(aut);
		FAState[] q = {q0, q1, q2, q3, q4, q5, q6};
		for(int i = 1; i < q.length; i ++) {
			for(int j = 3; j < q.length ; j ++) {
				if(i != j) System.out.println(path.checkPath(q[i], q[j]));
				else {
					System.out.println("" + i);
				}
			}
		}
		
		path.setSourceState(q4);
		path.setTargetState(q4);
		Pair<List<FAState>, List<String>> cycle = path.findCycle();
		System.out.println(cycle.getLeft());
		System.out.println(cycle.getRight());
		
		path.setSourceState(q2);
		path.setTargetState(q2);
		cycle = path.findCycle();
		System.out.println(cycle.getLeft());
		System.out.println(cycle.getRight());
		
		path.setSourceState(q0);
		path.setTargetState(q4);
		
		path.findPath();
		cycle = path.getPath();
		System.out.println(cycle.getLeft());
		System.out.println(cycle.getRight());
		
		List<String> prefix = new ArrayList<>();
		List<String> suffix = new ArrayList<>();
		prefix.add("a");
		suffix.add("b");
		suffix.add("a");
		FiniteAutomaton product = ProductBuilder.build(aut, prefix, suffix);
		EmptinessCheck checker = new EmptinessCheck(product);
		boolean result = checker.isEmpty();
		if(result) {
			System.err.println("Error, word should be in the automaton");
			System.exit(-1);
		}
		checker.findpath();
		
		System.out.println("prefix: " + checker.getInifinteWord().getLeft());
		System.out.println("suffix: " + checker.getInifinteWord().getRight());
		
		prefix.clear();
		suffix.clear();
		prefix.add("a");
		suffix.add("b");
		suffix.add("a");
		suffix.add("a");
		
		System.out.println("find path for (a, baa)");
		aut = new FiniteAutomaton("C:/Users/liyong/workspace/rabittest/" + "normbaa.ba");
		
		System.out.println("aut: ");
		AutomatonPrinter.print(aut, System.out);
		product = ProductBuilder.build(aut, prefix, suffix);
		AutomatonPrinter.print(product, System.out);
		checker = new EmptinessCheck(product);
		result = checker.isEmpty();
		if(result) {
			System.err.println("Error, word should be in the automaton");
			System.exit(-1);
		}
		checker.findpath();
		
		System.out.println("prefix: " + checker.getInifinteWord().getLeft());
		System.out.println("suffix: " + checker.getInifinteWord().getRight());
		
	}
}

/*
 *   function Dijkstra(Graph, source):
2      dist[source] ¡û 0                                    // Initialization
3
4      create vertex set Q
5
6      for each vertex v in Graph:           
7          if v ¡Ù source
8              dist[v] ¡û INFINITY                          // Unknown distance from source to v
9              prev[v] ¡û UNDEFINED                         // Predecessor of v
10
11         Q.add_with_priority(v, dist[v])
12
13
14     while Q is not empty:                              // The main loop
15         u ¡û Q.extract_min()                            // Remove and return best vertex
16         for each neighbor v of u:                       // only v that is still in Q
17             alt = dist[u] + length(u, v) 
18             if alt < dist[v]
19                 dist[v] ¡û alt
20                 prev[v] ¡û u
21                 Q.decrease_priority(v, alt)
22
23     return dist[], prev[]
*/
package oracle;

import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.Pair;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;

public class EmptinessChecker {
	
	int index = 0;
	Stack<FAState> S = new Stack<>();
	FiniteAutomaton fa;
	TreeMap<Integer, Integer> v_index = new TreeMap<>();
	TreeMap<Integer, Integer> v_lowlink = new TreeMap<>();
	// two states which should be visited infinitely often
	private FAState f_1 = null;
	private FAState f_2 = null;
	private Set<FAState> scc = new TreeSet<>();
	private Set<FAState> a_f;
	private Set<FAState> b_f;
	private WordFinder wordFinder;

	public EmptinessChecker(FiniteAutomaton fa, Set<FAState> f1, Set<FAState> f2) {
		this.fa = fa;
		this.a_f = f1;
		this.b_f = f2;
	}

	public boolean isEmpty() {
		for (FAState s : this.a_f) {
			if ((!this.v_index.containsKey(s.id)) && (tarjan(s))) {
				return false;
			}
		}
		for (FAState s : this.b_f) {
			if ((!this.v_index.containsKey(s.id)) && (tarjan(s))) {
				return false;
			}
		}
		return true;
	}

	boolean tarjan(FAState v) {
		
		this.v_index.put(v.id, this.index);
		this.v_lowlink.put(v.id, this.index);
		this.index += 1;
		this.S.push(v);
		Iterator<String> next_it = v.nextIt();

		while (next_it.hasNext()) {
			String next = next_it.next();
			Iterator<FAState> st_it = v.getNext(next).iterator();
			while(st_it.hasNext()) {
				FAState v_prime = st_it.next();
				if (! this.v_index.containsKey(v_prime.id)) {
					if (tarjan(v_prime)) {
						return true;
					}
					this.v_lowlink.put(v.id,
							Math.min(this.v_lowlink.get(v.id), this.v_lowlink.get(v_prime.id)));
				} else if (this.S.contains(v_prime)) {
					this.v_lowlink.put(v.id,
							Math.min(this.v_lowlink.get(v.id), this.v_index.get(v_prime.id)));
				}
			}
		}
		boolean isAcc = false;
		if (this.v_lowlink.get(v.id).intValue() == this.v_index.get(v.id).intValue()) {
			int numStates = 0;
			FAState state = null;
			this.scc.clear();
			boolean left = false;
			boolean right = false;
			while (!this.S.empty()) {
				FAState t = this.S.pop();
				numStates++;
				if (this.a_f.contains(t)) {
					this.f_1 = t;
					left = true;
				}
				if (this.b_f.contains(t)) {
					this.f_2 = t;
					right = true;
				}
				state = t;
				this.scc.add(t);
				if (t.id == v.id) {
					break;
				}
			}
			if ((numStates == 1) && ((state.getNext() == null) || (!state.getNext().contains(state)))) {
				return false;
			}
			isAcc = (left) && (right);
		}
		return isAcc;
	}

	Pair<List<FAState>, List<FAState>> run = null;
	Pair<List<String>, List<String>> word = null;

	public void findpath() {
		if ((this.f_1 == null) || (this.f_2 == null)) {
			return;
		}
		this.wordFinder = new WordFinder(this.fa, this.f_1, this.f_2, this.scc);
		this.wordFinder.computePath();
	}

	public WordFinder getWordFinder() {
		return this.wordFinder;
	}
}

package oracle;

import automata.FAState;
import automata.FiniteAutomaton;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class WordFinder {
	private FiniteAutomaton fa;
	private FAState f_1;
	private FAState f_2;
	private Set<FAState> scc;
	private List<String> wordPrefix;
	private List<String> wordSuffix;
	private List<FAState> runPrefix;
	private List<FAState> runSuffix;

	WordFinder(FiniteAutomaton fa, FAState f_1, FAState f_2, Set<FAState> scc) {
		this.fa = fa;
		this.f_1 = f_1;
		this.f_2 = f_2;
		this.scc = scc;
		this.wordPrefix = new ArrayList<>();
		this.wordSuffix = new ArrayList<>();
		this.runPrefix = new ArrayList<>();
		this.runSuffix = new ArrayList<>();
	}

	public void computePath() {
		computePrefix();
		computeSuffix();
	}

	private void computePrefix() {
		FAState init = this.fa.getInitialState();

		BitSet allStates = new BitSet(this.fa.states.size());
		allStates.set(0, allStates.size() - 1);

		this.runPrefix.add(init);
		findPath(init, this.f_1, allStates, true);
	}

	private void computeSuffix() {
		this.runSuffix.add(this.f_1);
		if (this.f_1 == this.f_2) {
			// check whether it has self-loop
			Iterator<String> labels = this.f_1.nextIt();
			while (labels.hasNext()) {
				String label = labels.next();
				Set<FAState> v_prime = this.f_1.getNext(label);
				for (FAState v : v_prime) {
					if (this.f_1.id == v.id) {
						this.wordSuffix.add(label);
						break;
					}
				}
				// has self-loop
				if (!this.wordSuffix.isEmpty()) {
					return;
				}
			}
		}
		// no self-loop has been found
		BitSet states = new BitSet(this.scc.size());
		FAState t = null;
		for (FAState s : this.scc) {
			// states which should be visited
			states.set(s.id);
			if ((this.f_1 == this.f_2) && (this.f_1 != s) && (this.f_1.getNext().contains(s))) {
				t = s;
			}
		}
		if (t != null) {
			this.f_2 = t;
		}
		findPath(this.f_1, this.f_2, states, false);
		findPath(this.f_2, this.f_1, states, false);
	}

	private void findPath(FAState s, FAState t, BitSet states, boolean prefix) {
		Map<FAState, FAState> preds = new HashMap<>();
		Map<FAState, String> predElems = new HashMap<>();

		BitSet visited = new BitSet();
		Queue<FAState> queue = new LinkedList<>();
		queue.add(s);
		visited.set(s.id);
		while( !queue.isEmpty()) {
			// have reached state t
			if (visited.get(t.id)) {
				break;
			}
			FAState cur = queue.poll();
			Iterator<String> it_elem = cur.nextIt();
			while(it_elem.hasNext()) {
				String elem = it_elem.next();
				Set<FAState> v_prime = cur.getNext(elem);
				for (FAState vp : v_prime) {
					if (! visited.get(vp.id)) {
						queue.add(vp);
						preds.put(vp, cur);
						predElems.put(vp, elem);
						visited.set(vp.id);
					}
				}
			}
		}
		LinkedList<FAState> run = new LinkedList<>();
		LinkedList<String> word = new LinkedList<>();
		FAState cur = t;
		while (cur != s) {
			run.addFirst(cur);
			word.addFirst(predElems.get(cur));
			cur = preds.get(cur);
		}
		List<String> w;
		List<FAState> r;
		if (prefix) {
			r = this.runPrefix;
			w = this.wordPrefix;
		} else {
			r = this.runSuffix;
			w = this.wordSuffix;
		}
		for (FAState state : run) {
			r.add(state);
		}

		for (String letter : word) {
			w.add(letter);
		}
	}

	public List<String> getWordPrefix() {
		return this.wordPrefix;
	}

	public List<String> getWordSuffix() {
		return this.wordSuffix;
	}

	public List<FAState> getRunSuffix() {
		return this.runSuffix;
	}

	public List<FAState> getRunPrefix() {
		return this.runPrefix;
	}
}

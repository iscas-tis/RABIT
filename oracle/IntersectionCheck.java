package oracle;

import automata.FAState;
import automata.FiniteAutomaton;
import datastructure.Pair;
import mainfiles.RABIT;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;

public class IntersectionCheck {
	private FiniteAutomaton c;
	private EmptinessChecker checker;
	private Set<FAState> f_1;
	private Set<FAState> f_2;

	public IntersectionCheck(FiniteAutomaton a, FiniteAutomaton b) {
		assert ((a != null) && (b != null));
		this.c = build(a, b);

		this.checker = new EmptinessChecker(this.c, this.f_1, this.f_2);
	}

	public boolean checkEmptiness() {
		return this.checker.isEmpty();
	}

	public void computePath() {
		this.checker.findpath();
	}

	public List<String> getPrefix() {
		return this.checker.getWordFinder().getWordPrefix();
	}

	public List<String> getSuffix() {
		return this.checker.getWordFinder().getWordSuffix();
	}

	public List<FAState> getRunPrefix() {
		return this.checker.getWordFinder().getRunPrefix();
	}

	public List<FAState> getRunSuffix() {
		return this.checker.getWordFinder().getRunSuffix();
	}

	private static int getStateId(int f, int d, int n) {
		return f * n + d;
	}

	private FiniteAutomaton build(FiniteAutomaton a, FiniteAutomaton b) {
		FiniteAutomaton c = new FiniteAutomaton();

		FAState cInit = c.createState();
		c.setInitialState(cInit);
		Map<Integer, FAState> cMap = new HashMap<>();

		FAState aInit = a.getInitialState();
		FAState bInit = b.getInitialState();

		int cId = getStateId(aInit.id, bInit.id, b.states.size());

		Map<Integer, FAState> aMap = new HashMap<>();
		Map<Integer, FAState> bMap = new HashMap<>();
		cMap.put(cId, cInit);
		for (FAState s : a.states) {
			aMap.put(s.id, s);
		}
		for (FAState s : b.states) {
			bMap.put(s.id, s);
		}
		this.f_1 = new TreeSet<>();
		this.f_2 = new TreeSet<>();
		if (a.F.contains(aInit)) {
			this.f_1.add(cInit);
		}
		if (b.F.contains(bInit)) {
			this.f_2.add(cInit);
		}
		Queue<Pair<Integer, Integer>> queue = new LinkedList<>();
		queue.add(new Pair<>(aInit.id, bInit.id));

		while (!queue.isEmpty()) {
			Pair<Integer, Integer> statePair = queue.poll();
			FAState aState = aMap.get(statePair.getLeft());
			FAState bState = bMap.get(statePair.getRight());
			cId = getStateId(statePair.getLeft(), statePair.getRight(), b.states.size());
			FAState cState = cMap.get(cId);

			Iterator<String> iter = bState.nextIt();
			while (iter.hasNext()) {
				String label = iter.next();
				Set<FAState> aSuccs = aState.getNext(label);
				Set<FAState> bSuccs = bState.getNext(label);
				if (aSuccs == null || bSuccs == null) {
					continue;
				}
				for (FAState aSucc : aSuccs) {
					for (FAState bSucc : bSuccs) {
						Pair<Integer, Integer> newPair = new Pair<>(aSucc.id, bSucc.id);
						cId = getStateId(aSucc.id, bSucc.id, b.states.size());
						FAState stateSucc = cMap.get(cId);
						// new state occurs
						if (stateSucc == null) {
							stateSucc = c.createState();
							queue.add(newPair);
							cMap.put(cId, stateSucc);
						}
						c.addTransition(cState, stateSucc, label);
						if (a.F.contains(aSucc)) {
							this.f_1.add(stateSucc);
						}
						if (b.F.contains(bSucc)) {
							this.f_2.add(stateSucc);
						}
					}
				}
			}
		}
		return c;
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

		AutomatonPrinter.print(aut, System.out);
		FiniteAutomaton c = new FiniteAutomaton();
		FAState c0 = c.createState();
		FAState c1 = c.createState();
		FAState c2 = c.createState();

		c.setInitialState(c0);
		c.F.add(c1);

		c.addTransition(c0, c1, "b");
		c.addTransition(c0, c1, "a");
		c.addTransition(c1, c2, "a");
		c.addTransition(c2, c1, "a");
		AutomatonPrinter.print(c, System.out);

		IntersectionCheck checker = new IntersectionCheck(aut, c);

		boolean r = checker.checkEmptiness();

		System.out.println(r);
		if (!r) {
			checker.computePath();
			System.out.println("prefix:" + checker.getPrefix());
			System.out.println("loop:" + checker.getSuffix());

			System.out.println("run prefix:" + checker.getRunPrefix());
			System.out.println("run loop:" + checker.getRunSuffix());
		}
		boolean flag = true;
		if(flag) {
			return ;
		}
		String file1 = "/home/liyong/workspace-neon/rabit/0.6.ba";
		String file2 = "/home/liyong/workspace-neon/rabit/0.7.ba";

		FiniteAutomaton A = new FiniteAutomaton(file1);
		FiniteAutomaton B = new FiniteAutomaton(file2);

		System.out.println(RABIT.isIncluded(A, B));

		checker = new IntersectionCheck(A, B);

		r = checker.checkEmptiness();
		if (!r) {
			checker.computePath();
			System.out.println("prefix:" + checker.getPrefix());
			System.out.println("loop:" + checker.getSuffix());

			System.out.println("run prefix:" + checker.getRunPrefix());
			System.out.println("run loop:" + checker.getRunSuffix());
		}
	}
}

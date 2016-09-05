package kodkod.engine.smvlab;

import kodkod.engine.PrimitiveSolver;

public interface SMVSolver extends PrimitiveSolver {
	public void addVar(Object var);

	public void addFrozenVar(Object var);

	public void addInvar(Object var);

	public void addLTLSpec(Object var);

	public void valueOf(Object var, int state);

	public int states();

	public int loopState();
}

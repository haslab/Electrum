package kodkod.engine.satlab;

import kodkod.engine.WTargetPrimitiveSolver;

/**
 * A SAT solver with support for partial satisfaction with weights.
 * pt.uminho.haslab
 */

public interface WTargetSATSolver extends TargetSATSolver, WTargetPrimitiveSolver {
	/**
	 * Adds a weighted target.
	 * pt.uminho.haslab
	 * @param lit the target
	 * @param weight the weight
	 */
	public boolean addWeight(int lit, int weight);
}

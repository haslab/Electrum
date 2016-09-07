package kodkod.engine.config;

import kodkod.engine.PrimitiveFactory;

public interface TargetOptions<S extends PrimitiveFactory<?>> extends PardinusOptions<S> {

	/**
	 * Whether the solver to run in target-oriented mode. This is different than
	 * simply setting the target-oriented mode to default, since in that case
	 * the target-oriented constructs are still initialized, but ignored for
	 * that particular execution.
	 * 
	 * @return Whether to initialize target-oriented constructs.
	 */
	public boolean runTarget();

	/**
	 * Instructs the solver to run in target-oriented mode.
	 * 
	 * @param runTarget
	 *            Whether to initialize target-oriented constructs.
	 */
	public void setRunTarget(boolean runTarget);

	/**
	 * The target-oriented mode that will be followed by the solver.
	 * 
	 * @return the target-oriented mode followed by the solver.
	 */
	public TMode targetMode();

	/**
	 * Instructs the solver to solve the problem in a specific target-oriented
	 * mode. This assumes that the target-oriented constructs were initialized
	 * (i.e., runTarget() = true), even if running in default mode.
	 * 
	 * @param the
	 *            target-oriented mode followed by the solver.
	 */
	public void setTargetMode(TMode mode);

	public enum TMode {
		DEFAULT, FAR, CLOSE
	}

}

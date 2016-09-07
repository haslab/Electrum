package kodkod.engine.config;

import kodkod.engine.PrimitiveFactory;

public interface DecomposedOptions<S extends PrimitiveFactory<?>> extends PardinusOptions<S> {

	public void setThreads(int threads);

	public int threads();

	public DMode decomposedMode();

	public void setDecomposedMode(DMode mode);

	/**
	 * Sets specific options to the configuration solver. Unless this method is
	 * called, the overall decomposed options are used by the configuration
	 * solver. Once this method is called, changes to the decomposed options no
	 * longer affect the configuration solver.
	 * 
	 * @param opt
	 */
	public void setConfigOptions(PardinusOptions<S> opt);

	public PardinusOptions<S> configOptions();

	public enum DMode {
		BATCH, PARALLEL, HYBRID, INCREMENTAL, EXHAUSTIVE;
	}

}

package kodkod.engine.config;

import kodkod.engine.satlab.SATFactory;

public interface BoundedOptions extends PardinusOptions<SATFactory> {

	public int bitwidth();
	
	public void setBitwidth(int bitwidth);

}

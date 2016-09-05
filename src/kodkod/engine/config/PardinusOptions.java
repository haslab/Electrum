package kodkod.engine.config;

import kodkod.engine.PrimitiveFactory;

public interface PardinusOptions<F extends PrimitiveFactory<?>> {

	public F solver();

	public Reporter reporter();
	
	public void setReporter(Reporter reporter);
	
	public void setSolver(F solver);

}

package kodkod.engine.config;

import kodkod.engine.PrimitiveFactory;

public interface TemporalOptions<S extends PrimitiveFactory<?>> extends PardinusOptions<S> {

	public void setMaxTraceLength(int trace_length);

	public int maxTraceLength();

}

package kodkod.engine.smvlab;

import kodkod.engine.PrimitiveFactory;

public abstract class SMVFactory implements PrimitiveFactory<SMVSolver> {

	public abstract SMVSolver instance();

}

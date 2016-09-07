package kodkod.engine;

public interface PrimitiveSolver {

//	public abstract int numberOfVariables();
		
//	public abstract int numberOfClauses();
		
	public boolean solve();
	
	public void free();
	
//	public abstract void addVariables(int numVars);

//	public boolean addClause(C clause);
//	
//	public T valueOf(V var);

}	

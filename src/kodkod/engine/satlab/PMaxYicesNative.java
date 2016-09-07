package kodkod.engine.satlab;



/**
 * 
 * @author tmg
 *
 */

public class PMaxYicesNative extends NativeSolver implements WTargetSATSolver {


	private boolean makearray;
	protected long array = 0;
	

	
	static {
		loadLibrary(PMaxYicesNative.class);
	}

	
	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "PMaxYicesNative";
	}
	
	/**
	 * Returns a pointer to an instance of Yices.
	 * @return a pointer to an instance of Yices.
	 */
	private static native long make();
	private static native long allocArray();
	
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#free(int)
	 */
	void free(long peer){
		if(array!=0){		
			free(peer,array);
		//System.out.println("free");
			array = 0;
		}
	}
	
	protected native void free(long peer, long array);
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#addVariables(int, int)
	 */
	void addVariables(long peer, int numVariables){
		//System.out.println(peer);
		natAddVariables(peer,array,numVariables,(super.numberOfVariables()) - numVariables);
	}

	native long natAddVariables(long peer,long array,int numVariables, int currentVarCount);
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#addClause(int, int[])
	 */
	boolean addClause(long peer, int[] lits){
		boolean res = natAddClause(peer,lits,makearray, array);
		makearray = false;
		return res;
	}
	
	native boolean natAddClause(long peer,int[] lits,boolean makearray, long array);
	


	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#valueOf(int, int)
	 */
	native boolean valueOf(long peer, int literal);
	private int targetCount;
	
	public PMaxYicesNative(){
		super(make());
		makearray = true;
		array = allocArray();
		//System.out.println("new");
		targetCount = 0;
	}
	
	static {
		loadLibrary(PMaxYicesNative.class);
	}

	@Override
	native boolean solve(long peer);

	@Override
	public int numberOfTargets() {
		return targetCount;
	}

	@Override
	public boolean addTarget(int lit) {
		// TODO Auto-generated method stub
		targetCount++;
		return addTarget(super.peer(),lit,array);
	}
	
	native boolean addTarget(long peer ,int lit,long array);

	@Override
	public boolean clearTargets() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addWeight(int lit, int weight) {
		// TODO Auto-generated method stub
		return addWeight(super.peer(),lit,weight,array);
	}
	
	native boolean addWeight(long peer,int lit, int weight,long array);
}
	

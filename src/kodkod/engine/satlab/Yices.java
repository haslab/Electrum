package kodkod.engine.satlab;

/**
 * 
 * @author tmg
 *
 */


class Yices extends NativeSolver {

	
	private boolean makearray;
	protected long array = 0;
	
	/**
	 * Constructs a new Yices wrapper.
	 */
	public Yices() {
		super(make());
		makearray = true;
		array = allocArray();
	}
	
	static {
		loadLibrary(Yices.class);
	}

	
	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "Yices";
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
	 * @see kodkod.engine.satlab.NativeSolver#solve(int)
	 */
	native boolean solve(long peer);
	

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#valueOf(int, int)
	 */
	native boolean valueOf(long peer, int literal);

}

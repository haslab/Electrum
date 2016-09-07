/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2014-present, Nuno Macedo
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.engine.Solution;
import kodkod.engine.Statistics;

/**
 * 
 * @author nmm
 *
 */
public class DMonitorImpl implements DMonitor {

	private long config_times = -1;
	private Statistics config_stats = null;

	private boolean finished = false;
	private long sats = 0;
	private long vars = 0;
	private long clauses = 0;
	
	protected final List<DProblem> solutions = new ArrayList<DProblem>();
	private int configs = 0;
	private boolean amalgamated_solution = false;

	/* (non-Javadoc)
	 * @see kodkod.pardinus.DReporterI#newConfig(kodkod.engine.Solution)
	 */
	@Override
	public synchronized void newConfig(Solution config) {
		if (config_times < 0) {
			config_times = config.stats().translationTime();
			config_stats = config.stats();
		}
		config_times += config.stats().solvingTime();
		configs ++;
	}

	/* (non-Javadoc)
	 * @see kodkod.pardinus.DReporterI#newSolution(kodkod.pardinus.DSolution)
	 */
	@Override
	public synchronized void newSolution(DProblem sol) {
    	solutions.add(sol);
		if (sol.sat()) sats++;
		vars += sol.getSolution().stats().primaryVariables();
		clauses += sol.getSolution().stats().clauses();
	}
	
	/* (non-Javadoc)
	 * @see kodkod.pardinus.DReporterI#getSats()
	 */
	@Override
	public long getNumSATs() {
		return sats;
	}
	
	/* (non-Javadoc)
	 * @see kodkod.pardinus.DReporterI#getVars()
	 */
	@Override
	public long getTotalVars() {
		return vars;
	}
	
	/* (non-Javadoc)
	 * @see kodkod.pardinus.DReporterI#getClauses()
	 */
	@Override
	public long getTotalClauses() {
		return clauses;
	}

	@Override
	public void configsDone() {
		finished = true;
	}

	@Override
	public void done(boolean timeout) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void terminated(boolean timeout) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public long getNumRuns() {
		return solutions.size();
	}

	@Override
	public Statistics getConfigStats() {
		return config_stats;
	}

	@Override
	public long getConfigTimes() {
		return config_times;
	}

	@Override
	public boolean isConfigsDone() {
		return finished;
	}

	@Override
	public long getNumConfigs() {
		return configs;
	}

	@Override
	public void amalgamatedWon() {
		amalgamated_solution  = true;
	}

	@Override
	public boolean isAmalgamated() {
		return amalgamated_solution;
	}
	
}

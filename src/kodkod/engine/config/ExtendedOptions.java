/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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
package kodkod.engine.config;

import kodkod.engine.satlab.SATFactory;

/**
 * @author nmm
 */
public class ExtendedOptions extends Options implements Cloneable, BoundedOptions, DecomposedOptions<SATFactory>,
		TemporalOptions<SATFactory>, TargetOptions<SATFactory> {

	public ExtendedOptions() {
		super();
	}

	public ExtendedOptions(ExtendedOptions options) {
		super(options);
		this.setTargetMode(options.targetMode());
		this.setRunTarget(options.runTarget());
		this.setThreads(options.threads());
		this.setDecomposedMode(options.decomposedMode());
		this.setConfigOptions(options.configOptions());
		this.setMaxTraceLength(options.maxTraceLength());
	}

	// pt.uminho.haslab: target-oriented solving

	// pt.uminho.haslab
	private TMode target_mode = TMode.DEFAULT;
	private boolean runTarget = false;

	// pt.uminho.haslab
	@Override
	public TMode targetMode() {
		return target_mode;
	}

	// pt.uminho.haslab
	@Override
	public void setTargetMode(TMode mode) {
		target_mode = mode;
	}

	// pt.uminho.haslab
	@Override
	public boolean runTarget() {
		return runTarget;
	}

	// pt.uminho.haslab
	@Override
	public void setRunTarget(boolean runTarget) {
		this.runTarget = runTarget;
	}

	// pt.uminho.haslab: decomposed solving

	// pt.uminho.haslab
	private int threads = 4;

	// pt.uminho.haslab
	private DMode mode = DMode.BATCH;
	private PardinusOptions<SATFactory> configOptions = this;

	/**
	 * Sets the number of threads that will be launched in parallel.
	 * 
	 * @param threads
	 */
	// pt.uminho.haslab
	@Override
	public void setThreads(int threads) {
		this.threads = threads;
	}

	// pt.uminho.haslab
	@Override
	public int threads() {
		return threads;
	}

	// pt.uminho.haslab
	@Override
	public DMode decomposedMode() {
		return mode;
	}

	// pt.uminho.haslab
	@Override
	public void setDecomposedMode(DMode mode) {
		this.mode = mode;
	}

	@Override
	public void setConfigOptions(PardinusOptions<SATFactory> opt) {
		configOptions = opt;
	}

	@Override
	public PardinusOptions<SATFactory> configOptions() {
		return configOptions;
	}

	// pt.uminho.haslab: temporal solving

	// pt.uminho.haslab
	private int trace_length = 20;

	// pt.uminho.haslab
	@Override
	public void setMaxTraceLength(int trace_length) {
		this.trace_length = trace_length;
	}

	// pt.uminho.haslab
	@Override
	public int maxTraceLength() {
		return trace_length;
	}

}

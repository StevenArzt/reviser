package soot.jimple.interproc.ifds.test.original;

import heros.InterproceduralCFG;
import heros.solver.IFDSSolver;
import soot.SootMethod;
import soot.Unit;

/**
 * Interface for injecting new code into the generic test case
 */
public interface ITestHandler<D> {
	
	/**
	 * Method that is called before Soot is run the first time.
	 */
	public void initialize();
	
	/**
	 * Initializes the application classes if necessary.
	 */
	public void initApplicationClasses();
	
	/**
	 * Method that is called when the basic information leakage analysis is complete.
	 * Implement this method to perform additional test tasks.
	 * @param solver The solver that has performed the generic analysis
	 */
	public void extendBasicTest
		(InterproceduralCFG<Unit, SootMethod> icfg,
		IFDSSolver<Unit,D,SootMethod,InterproceduralCFG<Unit,SootMethod>> solver);
	
	/**
	 * Method that is called when the CFG shall be patched by the implementer
	 * @param phase The phase of the test being executed. This value starts with zero
	 * and is extended by one up to the number of phases minues one.
	 */
	public void patchGraph(int phase);
	
	/**
	 * Method that is called when the extended test after updating/rerunning shall be
	 * performed.
	 * @param solver The solver containing the results on the modified CFG.
	 * @param phase The phase of the test being executed. This value starts with zero
	 * and is extended by one up to the number of phases minues one.
	 */
	public void performExtendedTest
		(InterproceduralCFG<Unit, SootMethod> icfg,
		IFDSSolver<Unit,D,SootMethod,InterproceduralCFG<Unit,SootMethod>> solver,
		int phase);
	
	/**
	 * Gets the number of phases in this test
	 * @return The number of phases in this test
	 */
	public int getPhaseCount();
	
}

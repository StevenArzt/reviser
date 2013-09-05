package soot.jimple.interproc.ifds.test.original;

import heros.IFDSTabulationProblem;
import heros.InterproceduralCFG;
import heros.solver.IFDSSolver;

import java.io.File;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import soot.Local;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.toolkits.ide.exampleproblems.IFDSUninitializedVariables;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;

public class IFDSUninitializedVariablesJUnit {

	private final static int TEST_COUNT = 10;
	private final static String JUNIT_DIR = "test";
	private final static String CLASS_NAME = "org.junit.runner.JUnitCore";
	
	private Set<Local> computeResults(final String codeDir) {
//		extractVersion(codeDir);
		
		soot.G.reset();
 		final Set<Local> results = new HashSet<Local>();
 
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
//				Scene.v().getSootClass(className).setApplicationClass();
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				InterproceduralCFG<Unit, SootMethod> icfg = new JimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<Unit, Local, SootMethod, InterproceduralCFG<Unit, SootMethod>> problem =
					new IFDSUninitializedVariables(icfg);
				IFDSSolver<Unit,Local,SootMethod,InterproceduralCFG<Unit,SootMethod>> solver =
					new IFDSSolver<Unit,Local,SootMethod,InterproceduralCFG<Unit,SootMethod>>(problem);	

				long beforeSolver = System.nanoTime();
				System.out.println("Running solver...");
				solver.solve();
				System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
				
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit"); 
				Unit ret = meth.getActiveBody().getUnits().getPredOf(meth.getActiveBody().getUnits().getLast());
				results.addAll(solver.ifdsResultsAt(ret));
			}
		}));

		final String sootcp = codeDir + File.pathSeparator
				+ JUNIT_DIR + "/hamcrest-core-1.3.jar" + File.pathSeparator
				+ "/usr/lib/jvm/java-6-sun/jre/lib/rt.jar" + File.pathSeparator
				+ "/usr/lib/jvm/java-6-sun/jre/lib/jce.jar" + File.pathSeparator
				+ "C:\\Program Files\\Java\\jre7\\lib\\rt.jar" + File.pathSeparator
				+ "C:\\Program Files\\Java\\jre7\\lib\\jce.jar";
		System.out.println("Soot classpath: " + sootcp);
		
		soot.Main.v().run(new String[] {
				"-W",
				"-main-class", CLASS_NAME,
				"-process-path", codeDir,
				"-src-prec", "java",
//				"-pp",
				"-cp", sootcp,
//				"-no-bodies-for-excluded",
//				"-exclude", "java",
//				"-exclude", "javax",
				"-output-format", "none",
				"-p", "jb", "use-original-names:true",
				"-p", "cg.spark", "on",
//				"-p", "cg.spark", "verbose:true",
				CLASS_NAME } );
		return results;
	}

	private boolean checkVersion(String initialVersion, String updatedVersion) {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Checking version " + initialVersion + " -> " + updatedVersion + "...");
			Set<Local> results = computeResults(JUNIT_DIR + File.separator + updatedVersion);
			System.out.println(results);
		}
		return true;
	}
	
	@Test
	public void simpleTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-original.jar");
	}

	@Test
	public void addLocalTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-addVarTest.jar");
	}
	
	@Test
	public void redefineVarTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-redefineVarTest.jar");
	}

	@Test
	public void removeStmtTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-removeStmtTest.jar");
	}

	@Test
	public void removeAssignmentTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-removeAssignmentTest.jar");
	}

	@Test
	public void addCallNoAssignmentTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-addCallNoAssignmentTest.jar");
	}

	@Test
	public void addCallAssignmentTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-addCallAssignmentTest.jar");
	}

	@Test
	public void removeStmtFromLoopTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-removeStmtFromLoopTest.jar");
	}

	@Test
	public void redefineReturnTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.10-redefineReturnTest.jar");
	}

	@Test
	public void newVersionTestJU() {
		checkVersion("junit-4.10-original.jar", "junit-4.11-original.jar");
	}

}
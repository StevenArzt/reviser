package soot.jimple.interproc.ifds.test.original;

import heros.IFDSTabulationProblem;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.incremental.UpdatableWrapper;
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
import soot.jimple.toolkits.ide.exampleproblems.incremental.IFDSUninitializedVariables;
import soot.jimple.toolkits.ide.icfg.UpdatableJimpleBasedInterproceduralCFG;

public class IFDSUninitializedVariablesJUnitCommits {

	private final static int TEST_COUNT = 10;
	private final static String JUNIT_DIR = "JUnit Versions";
	private final static String CLASS_NAME = "org.junit.runner.JUnitCore";
		
	private Set<UpdatableWrapper<Local>> computeResults(final String codeDir) {
//		extractVersion(codeDir);
		
		soot.G.reset();
 		final Set<UpdatableWrapper<Local>> results = new HashSet<UpdatableWrapper<Local>>();
 
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
//				Scene.v().getSootClass(className).setApplicationClass();
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				UpdatableInterproceduralCFG<Unit, SootMethod> icfg =
						new UpdatableJimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatableWrapper<Local>, UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit, SootMethod>> problem =
					new IFDSUninitializedVariables(icfg);
				IFDSSolver<UpdatableWrapper<Unit>,UpdatableWrapper<Local>,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>> solver =
					new IFDSSolver<UpdatableWrapper<Unit>,UpdatableWrapper<Local>,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>>(problem);	

				long beforeSolver = System.nanoTime();
				System.out.println("Running solver...");
				solver.solve();
				System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
				
				SootMethod meth = Scene.v().getMainClass().getMethodByName("main"); 
				UpdatableWrapper<Unit> ret = icfg.wrap(meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast()));
				results.addAll(solver.ifdsResultsAt(ret));
			}
		}));

		final String sootcp = codeDir + File.separator + "bin" + File.pathSeparator
				+ JUNIT_DIR + "/lib/hamcrest-core-1.3.jar" + File.pathSeparator
				+ "/usr/lib/jvm/java-6-sun/jre/lib/rt.jar" + File.pathSeparator
				+ "/usr/lib/jvm/java-6-sun/jre/lib/jce.jar" + File.pathSeparator
				+ "C:\\Program Files\\Java\\jre7\\lib\\rt.jar" + File.pathSeparator
				+ "C:\\Program Files\\Java\\jre7\\lib\\jce.jar";
		System.out.println("Soot classpath: " + sootcp);
		
		soot.Main.v().run(new String[] {
				"-W",
				"-main-class", CLASS_NAME,
				"-process-path", codeDir + File.separator + "bin",
				"-src-prec", "java",
				"-allow-phantom-refs",
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
			computeResults(JUNIT_DIR + File.separator + updatedVersion);
		}
		return true;
	}
	
	@Test
	public void simpleTestJU_030720132221_031420132151() {
		checkVersion("030720132221", "031420132151");
	}

	@Test
	public void simpleTestJU_031420132151_031620130026() {
		checkVersion("031420132151", "031620130026");
	}

	@Test
	public void simpleTestJU_031620130026_031820131702() {
		checkVersion("031620130026", "031820131702");
	}

	@Test
	public void simpleTestJU_031820131702_032020132304() {
		checkVersion("031820131702", "032020132304");
	}

	@Test
	public void simpleTestJU_032020132304_032120131735() {
		checkVersion("032020132304", "032120131735");
	}

	@Test
	public void simpleTestJU_032120131735_032120132100() {
		checkVersion("032120131735", "032120132100");
	}

	@Test
	public void simpleTestJU_032120132100_032120132144() {
		checkVersion("032120132100", "032120132144");
	}

	@Test
	public void simpleTestJU_032120132144_032720132135() {
		checkVersion("032120132144", "032720132135");
	}

	@Test
	public void simpleTestJU_032720132135_032720132341() {
		checkVersion("032720132135", "032720132341");
	}

	@Test
	public void simpleTestJU_032720132341_032720132348() {
		checkVersion("032720132341", "032720132348");
	}

	@Test
	public void simpleTestJU_032720132348_040120132353() {
		checkVersion("032720132348", "040120132353");
	}

	@Test
	public void simpleTestJU_040120132353_042920132120() {
		checkVersion("040120132353", "042920132120");
	}

	@Test
	public void simpleTestJU_042920132120_043020131827() {
		checkVersion("042920132120", "043020131827");
	}

	@Test
	public void simpleTestJU_043020131827_050120130055() {
		checkVersion("043020131827", "050120130055");
	}

	@Test
	public void simpleTestJU_050120130055_050220131806() {
		checkVersion("050120130055", "050220131806");
	}

	@Test
	public void simpleTestJU_050220131806_050220131856() {
		checkVersion("050220131806", "050220131856");
	}

	@Test
	public void simpleTestJU_050220131856_050720130016() {
		checkVersion("050220131856", "050720130016");
	}

	@Test
	public void simpleTestJU_050720130016_052720131836() {
		checkVersion("050720130016", "052720131836");
	}

	@Test
	public void simpleTestJU_052720131836_052720132001() {
		checkVersion("052720131836", "052720132001");
	}

	@Test
	public void simpleTestJU_052720132001_060520130242() {
		checkVersion("052720132001", "060520130242");
	}

	@Test
	public void simpleTestJU_060520130242_060520132159() {
		checkVersion("060520130242", "060520132159");
	}

	@Test
	public void simpleTestJU_060520132159_060620130028() {
		checkVersion("060520132159", "060620130028");
	}

	@Test
	public void simpleTestJU_060620130028_060620130722() {
		checkVersion("060620130028", "060620130722");
	}

	@Test
	public void simpleTestJU_060620130722_060620132234() {
		checkVersion("060620130722", "060620132234");
	}
	
}
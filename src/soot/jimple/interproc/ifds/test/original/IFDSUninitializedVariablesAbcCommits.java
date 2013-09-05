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

public class IFDSUninitializedVariablesAbcCommits {

	private final static int TEST_COUNT = 10;
	private final static String JUNIT_DIR = "abc Versions";
	private final static String CLASS_NAME = "abc.main.Main";
		
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

		final String sootcp = codeDir + File.separator + "classes" + File.pathSeparator
				+ JUNIT_DIR + "/lib/hamcrest-core-1.3.jar" + File.pathSeparator
				+ "/usr/lib/jvm/java-6-sun/jre/lib/rt.jar" + File.pathSeparator
				+ "/usr/lib/jvm/java-6-sun/jre/lib/jce.jar" + File.pathSeparator
				+ "C:\\Program Files\\Java\\jre7\\lib\\rt.jar" + File.pathSeparator
				+ "C:\\Program Files\\Java\\jre7\\lib\\jce.jar";
		System.out.println("Soot classpath: " + sootcp);
		
		soot.Main.v().run(new String[] {
				"-W",
				"-main-class", CLASS_NAME,
				"-process-path", codeDir + File.separator + "classes",
				"-src-prec", "java",
				"-allow-phantom-refs",
//				"-pp",
				"-cp", sootcp,
				"-no-bodies-for-excluded",
				"-exclude", "java",
				"-exclude", "javax",
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
	public void simpleTestAbc_200909021347_200909021404() {
		checkVersion("200909021347", "200909021404");
	}

	@Test
	public void simpleTestAbc_200909021404_200909021405() {
		checkVersion("200909021404", "200909021405");
	}

	@Test
	public void simpleTestAbc_200909021405_200909021406() {
		checkVersion("200909021405", "200909021406");
	}

	@Test
	public void simpleTestAbc_200909021406_200909071243() {
		checkVersion("200909021406", "200909071243");
	}

	@Test
	public void simpleTestAbc_200909071243_200909071317() {
		checkVersion("200909071243", "200909071317");
	}

	@Test
	public void simpleTestAbc_200909071317_200909071434() {
		checkVersion("200909071317", "200909071434");
	}

	@Test
	public void simpleTestAbc_200909071434_200909091000() {
		checkVersion("200909071434", "200909091000");
	}

	@Test
	public void simpleTestAbc_200909091000_200909091001() {
		checkVersion("200909091000", "200909091001");
	}

	@Test
	public void simpleTestAbc_200909091001_200910031237() {
		checkVersion("200909091001", "200910031237");
	}

	@Test
	public void simpleTestAbc_200910031237_200910031238() {
		checkVersion("200910031237", "200910031238");
	}

	@Test
	public void simpleTestAbc_200910031238_200910081643() {
		checkVersion("200910031238", "200910081643");
	}

	@Test
	public void simpleTestAbc_200910081643_200910261431() {
		checkVersion("200910081643", "200910261431");
	}

	@Test
	public void simpleTestAbc_200910261431_200910291810() {
		checkVersion("200910261431", "200910291810");
	}

	@Test
	public void simpleTestAbc_200910291810_201004301121() {
		checkVersion("200910291810", "201004301121");
	}

	@Test
	public void simpleTestAbc_201004301121_201005011732() {
		checkVersion("201004301121", "201005011732");
	}

	@Test
	public void simpleTestAbc_201005011732_201006041053() {
		checkVersion("201005011732", "201006041053");
	}

	@Test
	public void simpleTestAbc_201006041053_201009011057() {
		checkVersion("201006041053", "201009011057");
	}
	
	@Test
	public void simpleTestAbc_201009011057_201108161456() {
		checkVersion("201009011057", "201108161456");
	}

	@Test
	public void simpleTestAbc_201108161456_201108170943() {
		checkVersion("201108161456", "201108170943");
	}

	@Test
	public void simpleTestAbc_201108170943_201109060818() {
		checkVersion("201108170943", "201109060818");
	}

	@Test
	public void simpleTestAbc_201109060818_201201061648() {
		checkVersion("201109060818", "201201061648");
	}

	@Test
	public void simpleTestAbc_201201061648_201210190454() {
		checkVersion("201201061648", "201210190454");
	}

	@Test
	public void simpleTestAbc_201210190454_201306271843() {
		checkVersion("201210190454", "201306271843");
	}

	@Test
	public void simpleTestAbc_201306271843_201307121737() {
		checkVersion("201306271843", "201307121737");
	}
	
}
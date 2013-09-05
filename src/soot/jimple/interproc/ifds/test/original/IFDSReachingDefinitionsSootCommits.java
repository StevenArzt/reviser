package soot.jimple.interproc.ifds.test.original;

import heros.IFDSTabulationProblem;
import heros.InterproceduralCFG;
import heros.solver.IFDSSolver;

import java.io.File;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.toolkits.ide.exampleproblems.IFDSReachingDefinitions;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.toolkits.scalar.Pair;

public class IFDSReachingDefinitionsSootCommits {

	private final static int TEST_COUNT = 10;
	private final static String JUNIT_DIR = "soot Versions";
	private final static String CLASS_NAME = "soot.Main";

	private Set<Pair<Value, Set<DefinitionStmt>>> computeResults(final String codeDir) {
//		extractVersion(codeDir);
		
		soot.G.reset();
 		final Set<Pair<Value, Set<DefinitionStmt>>> results = new HashSet<Pair<Value, Set<DefinitionStmt>>>();
 
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
//				Scene.v().getSootClass(className).setApplicationClass();
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				InterproceduralCFG<Unit, SootMethod> icfg = new JimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<Unit, Pair<Value, Set<DefinitionStmt>>, SootMethod,
							InterproceduralCFG<Unit, SootMethod>> problem =
					new IFDSReachingDefinitions(icfg);
				IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
							InterproceduralCFG<Unit,SootMethod>> solver =
					new IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
							InterproceduralCFG<Unit,SootMethod>>(problem);	

				long beforeSolver = System.nanoTime();
				System.out.println("Running solver...");
				solver.solve();
				System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
				
				SootMethod meth = Scene.v().getMainClass().getMethodByName("main"); 
				Unit ret = meth.getActiveBody().getUnits().getPredOf(meth.getActiveBody().getUnits().getLast());
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
				"-process-path", codeDir + File.separator + "classes",
				"-src-prec", "java",
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
	public void simpleTestSoot_201306040837_201306041738() {
		checkVersion("201306040837", "201306041738");
	}

	@Test
	public void simpleTestSoot_201306041738_201306061001() {
		checkVersion("201306041738", "201306061001");
	}

	@Test
	public void simpleTestSoot_201306061001_201306061858() {
		checkVersion("201306061001", "201306061858");
	}

	@Test
	public void simpleTestSoot_201306061858_201306131547() {
		checkVersion("201306061858", "201306131547");
	}

	@Test
	public void simpleTestSoot_201306131547_201306140947() {
		checkVersion("201306131547", "201306140947");
	}

	@Test
	public void simpleTestSoot_201306140947_201306141844() {
		checkVersion("201306140947", "201306141844");
	}

	@Test
	public void simpleTestSoot_201306141844_201306151219() {
		checkVersion("201306141844", "201306151219");
	}

	@Test
	public void simpleTestSoot_201306151219_201306161541() {
		checkVersion("201306151219", "201306161541");
	}

	@Test
	public void simpleTestSoot_201306161541_201306161548() {
		checkVersion("201306161541", "201306161548");
	}

	@Test
	public void simpleTestSoot_201306161548_201306162138() {
		checkVersion("201306161548", "201306162138");
	}

	@Test
	public void simpleTestSoot_201306162138_201306192053() {
		checkVersion("201306162138", "201306192053");
	}

	@Test
	public void simpleTestSoot_201306192053_201306200925() {
		checkVersion("201306192053", "201306200925");
	}

	@Test
	public void simpleTestSoot_201306200925_201306201648() {
		checkVersion("201306200925", "201306201648");
	}

	@Test
	public void simpleTestSoot_201306201648_201306261912() {
		checkVersion("201306201648", "201306261912");
	}

	@Test
	public void simpleTestSoot_201306261912_201306270212() {
		checkVersion("201306261912", "201306270212");
	}

	@Test
	public void simpleTestSoot_201306270212_201306281749() {
		checkVersion("201306270212", "201306281749");
	}

	@Test
	public void simpleTestSoot_201306281749_201307011116() {
		checkVersion("201306281749", "201307011116");
	}

	@Test
	public void simpleTestSoot_201307011116_201307021644() {
		checkVersion("201307011116", "201307021644");
	}

	@Test
	public void simpleTestSoot_201307021644_201307021649() {
		checkVersion("201307021644", "201307021649");
	}

	@Test
	public void simpleTestSoot_201307021649_201307041303() {
		checkVersion("201307021649", "201307041303");
	}

	@Test
	public void simpleTestSoot_201307041303_201307042149() {
		checkVersion("201307041303", "201307042149");
	}

	@Test
	public void simpleTestSoot_201307042149_201307042220() {
		checkVersion("201307042149", "201307042220");
	}

	@Test
	public void simpleTestSoot_201307042220_201307051815() {
		checkVersion("201307042220", "201307051815");
	}

	@Test
	public void simpleTestSoot_201307051815_201307051826() {
		checkVersion("201307051815", "201307051826");
	}
	
}
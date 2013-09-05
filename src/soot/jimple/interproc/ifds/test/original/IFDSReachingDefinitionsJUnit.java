package soot.jimple.interproc.ifds.test.original;

import heros.IFDSTabulationProblem;
import heros.InterproceduralCFG;
import heros.solver.IFDSSolver;
import heros.util.Utils;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import soot.G;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.Singletons;
import soot.SootClass;
import soot.SootMethod;
import soot.SootResolver;
import soot.Transform;
import soot.Unit;
import soot.Value;
import soot.JastAddJ.CompilationUnit;
import soot.JastAddJ.Program;
import soot.jimple.DefinitionStmt;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.toolkits.ide.exampleproblems.IFDSReachingDefinitions;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.toolkits.scalar.Pair;

public class IFDSReachingDefinitionsJUnit {

	private final static int TEST_COUNT = 10;

	private abstract class DynamicTestHandler implements ITestHandler<Pair<Value, Set<DefinitionStmt>>> {
		
		private final static boolean PATCH_LIBRARIES = true;
		
		private final String originalFile;
		private final String patchedFile;
		private final String targetFile;
		
		public DynamicTestHandler(String originalFile, String patchedFile, String targetFile) {
			this.originalFile = originalFile;
			this.patchedFile = patchedFile;
			this.targetFile = targetFile;
		}
		
		@Override
		public void initialize() {
			try {
				String curDir = System.getProperty("user.dir");
				Utils.copyFile(curDir + "/test/" + originalFile, curDir + "/test/" + targetFile);
			} catch (IOException e) {
				Assert.fail(e.getMessage());
			}
		}

		@Override
		public void patchGraph(int phase) {
			final boolean AGGRESSIVE_CHECKS = true;
			
			// Get the original call graph size before we change anything
			System.out.println("Original call graph has " + Scene.v().getCallGraph().size() +  " edges");
			
			try {
				String curDir = System.getProperty("user.dir");
				Utils.copyFile(curDir + "/test/" + patchedFile, curDir + "/test/" + targetFile);
			} catch (IOException e) {
				Assert.fail(e.getMessage());
			}
		
			// Mark all existing compilation units as unresolved
			Program program = SootResolver.v().getProgram();
			for (CompilationUnit cu : program.getCompilationUnits())
				program.releaseCompilationUnitForFile(cu.pathName());

			// Load a new version of the source file into Soot

			// Release some stale scene information
			try {
				Field vcField = Singletons.class.getDeclaredField("instance_soot_jimple_toolkits_callgraph_VirtualCalls");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_toolkits_pointer_DumbPointerAnalysis");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_toolkits_pointer_FullObjectSet");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				
				vcField = Singletons.class.getDeclaredField("instance_soot_EntryPoints");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);

				vcField = Scene.class.getDeclaredField("doneResolving");
				vcField.setAccessible(true);
				vcField.set(Scene.v(), false);
				
				// Spark data
				Method methClear = HashMap.class.getMethod("clear");
				vcField = G.class.getDeclaredField("Parm_pairToElement");
				vcField.setAccessible(true);
				methClear.invoke(vcField.get(G.v()), (Object[]) null);

				vcField = G.class.getDeclaredField("MethodPAG_methodToPag");
				vcField.setAccessible(true);
				methClear.invoke(vcField.get(G.v()), (Object[]) null);
				
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_sets_AllSharedListNodes");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_sets_AllSharedHybridNodes");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_fieldrw_FieldTagger");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_pag_ArrayElement");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_fieldrw_FieldReadTagAggregator");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_fieldrw_FieldWriteTagAggregator");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_fieldrw_FieldTagAggregator");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_sets_EmptyPointsToSet");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_spark_SparkTransformer");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				
				vcField = Singletons.class.getDeclaredField("instance_soot_jimple_toolkits_pointer_FullObjectSet");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);

				vcField = G.class.getDeclaredField("newSetFactory");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
				vcField = G.class.getDeclaredField("oldSetFactory");
				vcField.setAccessible(true);
				vcField.set(G.v(), null);
			} catch (NoSuchFieldException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (SecurityException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (IllegalArgumentException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (NoSuchMethodException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InvocationTargetException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			Scene.v().setDefaultThrowAnalysis(null);
			Scene.v().releaseFastHierarchy();
			Scene.v().releaseReachableMethods();
			Scene.v().releaseActiveHierarchy();
			Scene.v().releasePointsToAnalysis();
			Scene.v().releaseCallGraph();
			Scene.v().setEntryPoints(null);

			// Force a resolve of all soot classes in the scene. We
			// need to copy the list to avoid ConcurrentModificationExceptions.
			Set<SootClass> ac = new HashSet<SootClass>();
			Set<SootClass> lc = new HashSet<SootClass>();
			Set<SootClass> allClasses = new HashSet<SootClass>();
			Set<String> methodBodies = new HashSet<String>();
			for (SootClass sc : Scene.v().getApplicationClasses()) {
				ac.add(sc);
				allClasses.add(sc);
			}
			if (PATCH_LIBRARIES)
				for (SootClass sc : Scene.v().getLibraryClasses()) {
					lc.add(sc);
					allClasses.add(sc);
				}
			for (SootClass sc : Scene.v().getClasses())
				allClasses.add(sc);
			for (SootClass sc : allClasses)
				for (SootMethod sm : sc.getMethods())
					if (sm.hasActiveBody())
						methodBodies.add(sm.getSignature());
			for (SootClass sc : allClasses) {
				// Remove the class from the scene so that it can be
				// added anew. This helps fixing Soot's internal caches.
				Scene.v().removeClass(sc);
				assert !Scene.v().containsClass(sc.getName());

				// Let the class think it has not been resolved yet. This
				// is important as resolving is aborted if the current
				// resolving level is greater than or equal to the requested
				// one.
				sc.setResolvingLevel(SootClass.DANGLING);
			}

			if (PATCH_LIBRARIES) {
				// Make sure that we load all class dependencies of the new version
				Scene.v().loadNecessaryClasses();
			}

			// Reload all application classes
			List<SootClass> newClasses = new ArrayList<SootClass>();
			for (SootClass sc : allClasses) {
				// Force a new class resolving
				SootClass scNew = Scene.v().forceResolve(sc.getName(), SootClass.SIGNATURES);
//				SootClass scNew = Scene.v().forceResolve(sc.getName(), SootClass.BODIES);
				assert scNew != null;
				if (ac.contains(sc))
					scNew.setApplicationClass();
				if (lc.contains(sc))
					scNew.setLibraryClass();
				assert !AGGRESSIVE_CHECKS || scNew != ac;
				assert scNew.isInScene();
				assert Scene.v().getSootClass(sc.getName()) == scNew;
				newClasses.add(scNew);

				for (SootMethod sm : scNew.getMethods())
					if (sm.isConcrete() && methodBodies.contains(sm.getSignature()))
						sm.retrieveActiveBody();
			}
			
			// Fix cached main class - this will automatically fix the main method
			SootClass oldMainClass = Scene.v().getMainClass();
			SootClass mainClass = Scene.v().getSootClass(oldMainClass.getName());
			Scene.v().setMainClass(mainClass);
			System.out.println("Old main class: " + oldMainClass + " - new: " + mainClass);
			assert !AGGRESSIVE_CHECKS || !oldMainClass.isInScene();

			// Patch the entry points
			long timeBeforeEP = System.nanoTime();
			Scene.v().getEntryPoints();
			System.out.println("Updating entry points took "
					+ ((System.nanoTime() - timeBeforeEP) / 1E9) + " seconds");

			// Recreate the exception throw analysis
			Scene.v().getDefaultThrowAnalysis();
			
			// Update the call graph
			long timeBeforeCG = System.nanoTime();
			PackManager.v().getPack("cg").apply();
			int cgSize = Scene.v().getCallGraph().size();
			System.out.println("Updating callgraph took "
					+ ((System.nanoTime() - timeBeforeCG) / 1E9) + " seconds, "
					+ "callgraph now has " + cgSize + " edges.");

			// Invalidate the list of reachable methods. It will automatically be recreated
			// on the next call to "getReachableMethods".
			long timeBeforeRM = System.nanoTime();
			Scene.v().getReachableMethods();
			System.out.println("Updating reachable methods took "
					+ ((System.nanoTime() - timeBeforeRM) / 1E9) + " seconds");
			
			// Update the class hierarchy
			Scene.v().getActiveHierarchy();
			
			List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>();
			eps.addAll(Scene.v().getEntryPoints());
			ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator());
			reachableMethods.update();
			
			// Fix the resolving state for the old classes. Otherwise, access to the
			// fields and methods will be blocked and no diff can be performed.
			for (SootClass sc : allClasses)
				sc.setResolvingLevel(SootClass.BODIES);
		}
		
		@Override
		public int getPhaseCount() {
			return 1;
		}
	};
	
	/**
	 * Performs a generic test and calls the extension handler when it is complete.
	 * This method runs the analysis once, then modifies the program and afterwards
	 * dynamically updates the analysis results.
	 * @param handler The handler to call after finishing the generic information
	 * leakage analysis
	 * @param className The name of the test class to use
	 */
	private void performTestRerun(final ITestHandler<Pair<Value, Set<DefinitionStmt>>> handler, final String className) {
		soot.G.reset();
 		handler.initialize();
 
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
				Scene.v().getSootClass(className).setApplicationClass();
				long timeBefore = System.nanoTime();				
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
				
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit"); 
				Unit ret = meth.getActiveBody().getUnits().getPredOf(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				checkInitialLeaks(results);

				if (handler != null) {
					handler.extendBasicTest(icfg, solver);
					for (int i = 0; i < handler.getPhaseCount(); i++) {
						long nanoBeforePatch = System.nanoTime();
						handler.patchGraph(i);
						System.out.println("Graph patched in " + (System.nanoTime() - nanoBeforePatch) / 1E9 + " seconds.");

						Scene.v().getSootClass(className).setApplicationClass();

						IFDSTabulationProblem<Unit, Pair<Value, Set<DefinitionStmt>>, SootMethod,
									InterproceduralCFG<Unit, SootMethod>> problem2 =
							new IFDSReachingDefinitions(icfg = new JimpleBasedInterproceduralCFG());
						IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
									InterproceduralCFG<Unit,SootMethod>> solver2 =
							new IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
									InterproceduralCFG<Unit,SootMethod>>(problem2);	
						
						beforeSolver = System.nanoTime();
						System.out.println("Running solver...");
						solver2.solve();
						System.out.println("Solver (rerun) done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
						if (handler != null)
							handler.performExtendedTest(icfg, solver2, i);
						
//						solver2.dumpResults(className + "_Rerun.csv");
					}
				}
				System.out.println("Time elapsed: " + ((double) (System.nanoTime() - timeBefore)) / 1E9);
			}
		}));

		String os = System.getProperty("os.name");
		String cpSep = ":";
		if (os.contains("Windows"))
			cpSep = ";";
		
		String udir = System.getProperty("user.dir");
		String sootcp = udir + File.separator + "test/junit-4.10.jar" + cpSep
				+ udir + File.separator + "test/hamcrest-core-1.3.jar" + cpSep
				+ udir + File.separator + "bin" + cpSep
				+ "/usr/lib/jvm/java-6-sun/jre/lib/rt.jar" + cpSep
				+ "/usr/lib/jvm/java-6-sun/jre/lib/jce.jar" + cpSep
				+ "C:\\Program Files\\Java\\jre7\\lib\\rt.jar" + cpSep
				+ "C:\\Program Files\\Java\\jre7\\lib\\jce.jar";
		System.out.println("Soot classpath: " + sootcp);
		soot.Main.v().run(new String[] {
				"-W",
				"-main-class", className,
				"-process-path", udir + File.separator + "test",
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
				/*"-app",*/ className } );
	}

	protected void checkInitialLeaks(Set<Pair<Value, Set<DefinitionStmt>>> results) {
		boolean found = false;
		for (Pair<Value, Set<DefinitionStmt>> p : results) {
			if (p.getO1() instanceof Local && ((Local) p.getO1()).getName().contains("$"))
				for (DefinitionStmt def : p.getO2())
					if (def.toString().contains(("new org.junit.runner.JUnitCore"))) {
						found = true;
						break;
					}
			if (found) break;
		}
		Assert.assertTrue(found);

		for (Pair<Value, Set<DefinitionStmt>> p : results)
			if (p.getO1() instanceof Local)
				for (DefinitionStmt def : p.getO2())
					if (def.toString().contains("new org.junit.runner.notification.RunListener"))
						Assert.fail("Invalid initial leak found");
	}

	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerSimpleTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-original.jar", "junit-4.10.jar") {
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
				Unit u = meth.getActiveBody().getUnits().getPredOf(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(u);
				checkInitialLeaks(results);
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}
	
	/**
	 * Performs a simple analysis without any updates to the program graph
	 */
	@Test
	public void simpleTestJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting simpleTestJU_Rerun...");
			performTestRerun(ITestHandlerSimpleTest(), "org.junit.runner.JUnitCore");
			System.out.println("simpleTestJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerAddVarTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-addVarTest.jar", "junit-4.10.jar") {
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
				
				Unit ret = null;
				for (Unit u : meth.getActiveBody().getUnits())
					if (u.toString().equals("virtualinvoke $r1.<java.io.PrintStream: void println(java.lang.String)>(foo)")) {
						ret = u;
						break;
					}
				Assert.assertNotNull(ret);
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);

				boolean found = false;
				for (Pair<Value, Set<DefinitionStmt>> p : results) {
					if (p.getO1() instanceof Local)
						for (DefinitionStmt def : p.getO2())
							if (def.toString().contains(("= \"Hello World\""))) {
								found = true;
								break;
							}
					if (found) break;
				}
				Assert.assertTrue(found);

				ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				results = solver.ifdsResultsAt(ret);
				checkInitialLeaks(results);

				found = false;
				for (Pair<Value, Set<DefinitionStmt>> p : results) {
					if (p.getO1() instanceof Local)
						for (DefinitionStmt def : p.getO2())
							if (def.toString().contains(("= \"Hello World\""))) {
								found = true;
								break;
							}
					if (found) break;
				}
				Assert.assertTrue(found);
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then adds a local with an assignment
	 */
	@Test
	public void addLocalJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting addLocalJU_Rerun...");
			performTestRerun(ITestHandlerAddVarTest(), "org.junit.runner.JUnitCore");
			System.out.println("addLocalJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerRedefineVarTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-redefineVarTest.jar", "junit-4.10.jar") {
			
			private Unit originalPoint;
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				originalPoint = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(originalPoint);
				
				System.out.println("---------------------\nOld results:\n---------------------");
				for (Pair<Value, Set<DefinitionStmt>> p : results)
					System.out.println(p);
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit stmt = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				
				System.out.println("--------------------------");
				
				for (Unit u : meth.getActiveBody().getUnits()) {
					boolean found = false;
					List<Unit> unitQueue = new ArrayList<Unit>();
					Set<Unit> doneSet = new HashSet<Unit>();
					unitQueue.add(meth.getActiveBody().getUnits().getFirst());
					while (!unitQueue.isEmpty()) {
						Unit curUnit = unitQueue.remove(0);
						if (!doneSet.add(curUnit))
							continue;
						if (curUnit == u) {
							found = true;
							break;
						}
						for (Unit succ : icfg.getSuccsOf(curUnit))
							unitQueue.add(succ);
					}
					Assert.assertTrue("Statement not found: " + u, found);
//					System.out.println(u + "\t" + solver.ifdsResultsAt(icfg.wrapWeak(u)).size());
				}
				
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(stmt);
				Assert.assertTrue(((JimpleBasedInterproceduralCFG) icfg).containsStmt(stmt));
				
				System.out.println("---------------------\nNew results:\n---------------------");
				for (Pair<Value, Set<DefinitionStmt>> p : results)
					System.out.println(p);
				
				boolean found = false;
				for (Pair<Value, Set<DefinitionStmt>> p : results) {
					System.out.println(p);
					if (p.getO1() instanceof Local
							&& ((Local) p.getO1()).getName().contains("$")) {
						for (DefinitionStmt def : p.getO2())
							if (def.toString().contains("new org.junit.runner.notification.RunListener")) {
								found = true;
								break;
							}
					}
					if (found) break;
				}
				Assert.assertTrue(found);
			}

			@Override
			public void initApplicationClasses() {
			}
		};
	}

	/**
	 * Performs a simple analysis, then overwrites a local variable
	 */
	@Test
	public void redefineVarJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting redefineVarJU_Rerun...");
			performTestRerun(ITestHandlerRedefineVarTest(), "org.junit.runner.JUnitCore");
			System.out.println("redefineVarJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerRemoveStmtTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-removeStmtTest.jar", "junit-4.10.jar") {

			Set<Pair<Value, Set<DefinitionStmt>>> original = new HashSet<Pair<Value, Set<DefinitionStmt>>>();
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				original.addAll(results);
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				
				// The next line does not hold when running with Java libraries as
				// a whole chunk of code is no longer reachable with removes many
				// candidates from the points-to analysis, e.g. for the interator
				// invocation in r34. Therefore, we only check a weaker condition.
//				Assert.assertEquals(original.size(), results.size());
				for (Pair<Value, Set<DefinitionStmt>> pr : results) {
					boolean found = false;
					for (Pair<Value, Set<DefinitionStmt>> po : original)
						if (po.toString().equals(pr.toString())) {
							found = true;
							break;
						}
					Assert.assertTrue("Missing result: " + pr, found);
				}
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then removes a non-assignment statement
	 */
	@Test
	public void removeStmtJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting removeStmtJU_Rerun...");
			performTestRerun(ITestHandlerRemoveStmtTest(), "org.junit.runner.JUnitCore");
			System.out.println("removeStmtJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerRemoveAssignmentTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-removeAssignmentTest.jar", "junit-4.10.jar") {

			Set<Pair<Value, Set<DefinitionStmt>>> original = new HashSet<Pair<Value, Set<DefinitionStmt>>>();
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);

				System.out.println("-----------------------------\nOld results\n-----------------------------");
				original.addAll(results);
				for (Pair<Value, Set<DefinitionStmt>> p : results)
					System.out.println(p);
				System.out.println("-----------------------------");
				
				System.out.println("-----------------------------\nOld runMain() function\n-----------------------------");
				for (Unit u : meth.getActiveBody().getUnits())
					System.out.println(u);
				System.out.println("-----------------------------");
			}
			
			@Override
			public void patchGraph(int phase) {
				super.patchGraph(phase);

				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				System.out.println("-----------------------------\nNew runMain() function\n-----------------------------");
				for (Unit u : meth.getActiveBody().getUnits())
					System.out.println(u);
				System.out.println("-----------------------------");
				
				Scene.v().getSootClass("org.junit.internal.TextListener").setApplicationClass();
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				
				System.out.println("-----------------------------\nNew results\n-----------------------------");
				for (Pair<Value, Set<DefinitionStmt>> urd : results) {
					System.out.println(urd);
					
					if (urd.toString().equals("$r1 -> [$r0 = <java.lang.System: java.io.PrintStream out>]"))
						System.out.print("");
				}
				System.out.println("-----------------------------");
				
				Assert.assertEquals(original.size() - 1, results.size());
				for (Pair<Value, Set<DefinitionStmt>> pr : results)
					if (pr.getO1().toString().contains("listener"))
						Assert.assertTrue(pr.getO2().toString().contains(" = null"));
				/*
				for (UpdatableReachingDefinition pr : results) {
					boolean found = false;
					for (UpdatableReachingDefinition po : original)
						if (pr.getContents().toString().equals(po.getContents().toString())) {
							found = true;
							break;
						}
					if (!found) {
						// Doesn't work out as Soot assigns new names to the
						// temporary variables
//						Assert.assertTrue(pr.getContents().getO1().toString().contains("listener"));
//						Assert.assertTrue(pr.getContents().getO2().toString().contains(" = null]"));
					}
				}
				*/
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then removes an assignment statement
	 */
	@Test
	public void removeAssignmentJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting removeAssignmentJU_Rerun...");
			performTestRerun(ITestHandlerRemoveAssignmentTest(), "org.junit.runner.JUnitCore");
			System.out.println("removeAssignmentJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerAddCallNoAssignmentTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-addCallNoAssignmentTest.jar", "junit-4.10.jar") {

			Set<Pair<Value, Set<DefinitionStmt>>> original = new HashSet<Pair<Value, Set<DefinitionStmt>>>();
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				original.addAll(results);
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				
				Assert.assertEquals(original.size(), results.size());
				for (Pair<Value, Set<DefinitionStmt>> pr : results) {
					System.out.println(pr);
					boolean found = false;
					for (Pair<Value, Set<DefinitionStmt>> po : original)
						if (pr.toString().equals(po.toString())) {
							found = true;
							break;
						}
					Assert.assertTrue("Statement not found: " + pr, found);
				}
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then adds a call without creating a new assignment
	 */
	@Test
	public void addCallNoAssignmentJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting addCallNoAssignmentJU_Rerun...");
			performTestRerun(ITestHandlerAddCallNoAssignmentTest(), "org.junit.runner.JUnitCore");
			System.out.println("addCallNoAssignmentJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerAddCallAssignmentTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-addCallAssignmentTest.jar", "junit-4.10.jar") {

			Set<Pair<Value, Set<DefinitionStmt>>> original = new HashSet<Pair<Value, Set<DefinitionStmt>>>();
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				System.out.println("Original size: " + results.size());
				original.addAll(results);
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
			
				Assert.assertEquals(original.size(), results.size());
				for (Pair<Value, Set<DefinitionStmt>> po : original) {
					boolean found = false;
					for (Pair<Value, Set<DefinitionStmt>> pr : results)
						if (pr.toString().equals(po.toString())) {
							found = true;
							break;
						}
					if (!found) {
						System.out.println("FAILED: " + po);
						Assert.fail("Statement not found: " + po);
					}
				}
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then adds a call inside a new assignment
	 */
	@Test
	public void addCallAssignmentJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting addCallAssignmentJU_Rerun...");
			performTestRerun(ITestHandlerAddCallAssignmentTest(), "org.junit.runner.JUnitCore");
			System.out.println("addCallAssignmentJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerRemoveStmtFromLoopTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-removeStmtFromLoopTest.jar", "junit-4.10.jar") {

			Set<String> original = new HashSet<String>();
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				System.out.println("--ORIGINAL METHOD");
				for (Unit u : meth.getActiveBody().getUnits())
					System.out.println(u);
				
				Unit ret = meth.getActiveBody().getUnits().getLast();
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);

				System.out.println("--------------\nORIGINAL RESULTS\n--------------");
				for (Pair<Value, Set<DefinitionStmt>> p : results) {
					original.add(p.toString().replaceAll("(\\$r|l)\\d+", ""));
					System.out.println(p);
				}
				System.out.println("ORIGINAL size: " + results.size());
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
				System.out.println("--NEW METHOD");
				for (Unit u : meth.getActiveBody().getUnits())
					System.out.println(u);

				Unit ret = meth.getActiveBody().getUnits().getLast();
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);

				System.out.println("--------------\nNEW RESULTS\n--------------");
				for (Pair<Value, Set<DefinitionStmt>> pr : results)
					System.out.println(pr);

				for (String po : original)
				{
					boolean found = false;
					for (Pair<Value, Set<DefinitionStmt>> pr : results)
						if (po.equals(pr.toString().replaceAll("(\\$r|l)\\d+", "")))
							found = true;
					
					if (!found) {
						System.out.println("Missing statement: " + po);
						Assert.fail("Missing statement: " + po);
					}
				}

				Set<String> newResults = new HashSet<String>(results.size());
				for (Pair<Value, Set<DefinitionStmt>> pr : results) {
					String newRes = pr.toString().replaceAll("(\\$r|l)\\d+", "");
					newResults.add(newRes);

					boolean found = false;
					for (String po : original)
						if (newRes.equals(po)) {
							found = true;
							break;
						}
					if (!found) {
						System.out.println("New result: " + pr);
						Assert.assertEquals("c", pr.getO1().toString());
						Assert.assertEquals("[c = null]", pr.getO2().toString());
					}
				}
				
				Assert.assertEquals(original.size() + 1, newResults.size());
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then removes a call from a loop and adds an
	 * assignment to a new variable instead
	 */
	@Test
	public void removeStmtFromLoopJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting removeStmtFromLoopJU_Rerun...");
			performTestRerun(ITestHandlerRemoveStmtFromLoopTest(), "org.junit.runner.JUnitCore");
			System.out.println("removeStmtFromLoopJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerRedefineReturnTest() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.10-redefineReturnTest.jar", "junit-4.10.jar") {

			Set<Pair<Value, Set<DefinitionStmt>>> original = new HashSet<Pair<Value, Set<DefinitionStmt>>>();
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				original.addAll(results);
			}

			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
				Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
				
				Assert.assertEquals(original.size(), results.size());
				for (Pair<Value, Set<DefinitionStmt>> pr : results) {
					boolean found = false;
					for (Pair<Value, Set<DefinitionStmt>> po : original)
						if (pr.toString().equals(po.toString())) {
							found = true;
							break;
						}
					if (!found) {
						Assert.assertEquals("result", pr.getO1().toString());
						Assert.assertEquals("[result = null]", pr.getO2().toString());
					}
				}
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}

	/**
	 * Performs a simple analysis, then overwrites the return value of a called
	 * function and checks whether it is returned correctly
	 */
	@Test
	public void redefineReturnJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting redefineReturnJU_Rerun...");
			performTestRerun(ITestHandlerRedefineReturnTest(), "org.junit.runner.JUnitCore");
			System.out.println("redefineReturnJU_Rerun finished.");
		}
	}
	
	private ITestHandler<Pair<Value, Set<DefinitionStmt>>> ITestHandlerNewVersion() {
		return new DynamicTestHandler("junit-4.10-original.jar", "junit-4.11-original.jar", "junit-4.10.jar") {
			
			Set<Pair<Value, Set<DefinitionStmt>>> original;
			Set<Pair<Value, Set<DefinitionStmt>>> originalRM;
			Set<Pair<Value, Set<DefinitionStmt>>> originalAL1;
			Set<Pair<Value, Set<DefinitionStmt>>> originalALS;
			Set<Pair<Value, Set<DefinitionStmt>>> originalAL;
			Set<Pair<Value, Set<DefinitionStmt>>> originalRet;

			private Set<Pair<Value, Set<DefinitionStmt>>> getResultsAt
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					Unit unit) {
				Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(unit);
				System.out.println("RESULTS:\n-------------------");
				for (Pair<Value, Set<DefinitionStmt>> pr : results)
					System.out.println(pr);
				return results;
			}
			
			private void compareResults
					(Set<Pair<Value, Set<DefinitionStmt>>> original,
					Set<Pair<Value, Set<DefinitionStmt>>> updated,
					int offset) {
				System.out.println("NEW RESULTS:\n-------------------");
				for (Pair<Value, Set<DefinitionStmt>> pr : updated)
					System.out.println(pr);
				
//				Assert.assertEquals(original.size() + offset, updated.size());
				for (Pair<Value, Set<DefinitionStmt>> pr : original) {
					boolean found = false;
					for (Pair<Value, Set<DefinitionStmt>> po : updated)
						if (pr.toString().replaceAll("((\\$r|l)\\d+)|(\\w+\\$)|args", "").equals
								(po.toString().replaceAll("((\\$r|l)\\d+)|i\\$|(\\w+\\$)|args", ""))) {
							found = true;
							break;
						}
					if (!found)
						System.out.println("Missing result: " + pr);
					Assert.assertTrue("Missing: " + pr, found);
				}
				
			}
			
			@Override
			public void extendBasicTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver) {
				
				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
					Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
					original = getResultsAt(icfg, solver, ret);
				}
				
				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
					Unit ret = meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast());
					originalRM = getResultsAt(icfg, solver, ret);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("addListener");
					Unit ret = meth.getActiveBody().getUnits().getFirst();
					originalAL1 = getResultsAt(icfg, solver, ret);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("addListener");
					Unit ret = meth.getActiveBody().getUnits().getSuccOf
							(meth.getActiveBody().getUnits().getFirst());
					originalALS = getResultsAt(icfg, solver, ret);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("addListener");
					Unit ret = meth.getActiveBody().getUnits().getPredOf
							(meth.getActiveBody().getUnits().getLast());
					originalAL = getResultsAt(icfg, solver, ret);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("main");
					Unit ret = meth.getActiveBody().getUnits().getLast();
					originalRet = getResultsAt(icfg, solver, ret);
				}
			}
			
			@Override
			public void performExtendedTest
					(InterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<Unit,Pair<Value, Set<DefinitionStmt>>,SootMethod,
						InterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				
				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
					Unit ret = meth.getActiveBody().getUnits().getPredOf
							(meth.getActiveBody().getUnits().getLast());
					Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
					compareResults(original, results, 2);
				}
				
				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("runMain");
					Unit ret = meth.getActiveBody().getUnits().getPredOf
							(meth.getActiveBody().getUnits().getLast());
					Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
					compareResults(originalRM, results, 0);
						
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("addListener");
					Unit ret = meth.getActiveBody().getUnits().getFirst();
					Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
					compareResults(originalAL1, results, 0);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("addListener");
					Unit ret = meth.getActiveBody().getUnits().getSuccOf
							(meth.getActiveBody().getUnits().getFirst());
					Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
					compareResults(originalALS, results, 0);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("addListener");
					Unit ret = meth.getActiveBody().getUnits().getPredOf
							(meth.getActiveBody().getUnits().getLast());
					Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
					compareResults(originalAL, results, 0);
				}

				{
					SootMethod meth = Scene.v().getMainClass().getMethodByName("main");
					Unit ret = meth.getActiveBody().getUnits().getLast();
					Set<Pair<Value, Set<DefinitionStmt>>> results = solver.ifdsResultsAt(ret);
					compareResults(originalRet, results, 0);
				}
			}

			@Override
			public void initApplicationClasses() {
				// TODO Auto-generated method stub
				
			}
		};
	}
	
	/**
	 * Performs a simple analysis and then replaces the JUnit library with a
	 * newer version
	 */
	@Test
	public void newVersionJU_Rerun() {
		for (int i = 0; i < TEST_COUNT; i++) {
			System.out.println("Starting newVersionJU_Rerun...");
			performTestRerun(ITestHandlerNewVersion(), "org.junit.runner.JUnitCore");
			System.out.println("newVersionJU_Rerun finished.");
		}
	}

}
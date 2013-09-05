package soot.jimple.interproc.ifds.test;

import heros.IFDSTabulationProblem;
import heros.incremental.AbstractUpdatableInterproceduralCFG;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.incremental.UpdatableWrapper;
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
import soot.JastAddJ.CompilationUnit;
import soot.JastAddJ.Program;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.toolkits.ide.exampleproblems.incremental.IFDSPossibleTypes;
import soot.jimple.toolkits.ide.exampleproblems.incremental.UpdatablePossibleType;
import soot.jimple.toolkits.ide.icfg.UpdatableJimpleBasedInterproceduralCFG;

public class IFDSPossibleTypesPDFsam {

	private abstract class DynamicTestHandler implements ITestHandler<UpdatablePossibleType> {
			
		private final boolean PATCH_LIBRARIES = false;

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
		public void initApplicationClasses() {
		}
		
		@Override
		public int getPhaseCount() {
			return 1;
		}
	};
		
	/**
	 * Performs a generic test and calls the extension handler when it is complete.
	 * This method does not create indices for dynamic updates. Instead, updates are
	 * just propagated along the edges until a fix point is reached.
	 * @param handler The handler to call after finishing the generic information
	 * leakage analysis
	 * @param className The name of the test class to use
	 */
	private void performTestDirect(final ITestHandler<UpdatablePossibleType> handler, final String className) {
		soot.G.reset();
		handler.initialize();

		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
				Scene.v().getSootClass(className).setApplicationClass();
				
				handler.initApplicationClasses();
				
				long timeBefore = System.nanoTime();
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				AbstractUpdatableInterproceduralCFG<Unit, SootMethod> icfg = new UpdatableJimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatablePossibleType, UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit, SootMethod>> problem =
						new IFDSPossibleTypes(icfg);
				IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>> solver =
						new IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>>(problem);	
				
				long beforeSolver = System.nanoTime();
				System.out.println("Running solver...");
				solver.solve();
				System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
								
				if (handler != null) {
					handler.extendBasicTest(icfg, solver);
					for (int i = 0; i < handler.getPhaseCount(); i++) {
						long nanoBeforePatch = System.nanoTime();
						handler.patchGraph(i);
						System.out.println("Graph patched in " + (System.nanoTime() - nanoBeforePatch) / 1E9 + " seconds.");

						handler.initApplicationClasses();
						Scene.v().getSootClass(className).setApplicationClass();
						
						nanoBeforeCFG = System.nanoTime();
						icfg = new UpdatableJimpleBasedInterproceduralCFG();
						System.out.println("ICFG updated in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");
						
						long nanoBeforeUpdate = System.nanoTime();
						solver.update(icfg);
						System.out.println("IDE results updated in " + (System.nanoTime() - nanoBeforeUpdate) / 1E9 + " seconds.");						
						
						handler.performExtendedTest(icfg, solver, i);
//						solver.dumpResults(className + "_Propagate.csv");
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
		String sootcp = udir + File.separator + "test/pdfsam.jar" + cpSep
//				+ udir + File.separator + "hamcrest-core-1.3.jar" + cpSep
//				+ udir + File.separator + "bin" + cpSep
//				+ udir + File.separator + "javaws.jar" + cpSep
//				+ udir + File.separator + "j3dcore.jar" + cpSep
//				+ udir + File.separator + "j3dutils.jar" + cpSep
//				+ udir + File.separator + "vecmath.jar" + cpSep
//				+ udir + File.separator + "AppleJavaExtensions.jar" + cpSep
//				+ udir + File.separator + "jmf.jar" + cpSep
//				+ udir + File.separator + "sunflow.jar" + cpSep
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
				"-allow-phantom-refs",
				"-no-bodies-for-excluded",
				"-exclude", "java",
				"-exclude", "javax",
				"-output-format", "none",
				"-p", "jb", "use-original-names:true",
				"-p", "cg.spark", "on",
				"-app", className } );
	}

	/**
	 * Performs a generic test and calls the extension handler when it is complete.
	 * This method runs the analysis once, then modifies the program and afterwards
	 * dynamically updates the analysis results.
	 * @param handler The handler to call after finishing the generic information
	 * leakage analysis
	 * @param className The name of the test class to use
	 */
	private void performTestRerun(final ITestHandler<UpdatablePossibleType> handler, final String className) {
		soot.G.reset();
 		handler.initialize();
 
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
				Scene.v().getSootClass(className).setApplicationClass();
				long timeBefore = System.nanoTime();				
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				AbstractUpdatableInterproceduralCFG<Unit, SootMethod> icfg = new UpdatableJimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatablePossibleType, UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit, SootMethod>> problem =
					new IFDSPossibleTypes(icfg);
				IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>> solver =
					new IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>>(problem);	

				long beforeSolver = System.nanoTime();
				System.out.println("Running solver...");
				solver.solve();
				System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
				
				if (handler != null) {
					handler.extendBasicTest(icfg, solver);
					for (int i = 0; i < handler.getPhaseCount(); i++) {
						long nanoBeforePatch = System.nanoTime();
						handler.patchGraph(i);
						System.out.println("Graph patched in " + (System.nanoTime() - nanoBeforePatch) / 1E9 + " seconds.");

						Scene.v().getSootClass(className).setApplicationClass();

						IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatablePossibleType, UpdatableWrapper<SootMethod>,
									UpdatableInterproceduralCFG<Unit, SootMethod>> problem2 =
							new IFDSPossibleTypes(icfg = new UpdatableJimpleBasedInterproceduralCFG());
						IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
									UpdatableInterproceduralCFG<Unit,SootMethod>> solver2 =
							new IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
									UpdatableInterproceduralCFG<Unit,SootMethod>>(problem2);
						
						solver2.solve();
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
		String sootcp = udir + File.separator + "test/pdfsam.jar" + cpSep
//				+ udir + File.separator + "hamcrest-core-1.3.jar" + cpSep
//				+ udir + File.separator + "bin" + cpSep
//				+ udir + File.separator + "javaws.jar" + cpSep
//				+ udir + File.separator + "j3dcore.jar" + cpSep
//				+ udir + File.separator + "j3dutils.jar" + cpSep
//				+ udir + File.separator + "vecmath.jar" + cpSep
//				+ udir + File.separator + "AppleJavaExtensions.jar" + cpSep
//				+ udir + File.separator + "jmf.jar" + cpSep
//				+ udir + File.separator + "sunflow.jar" + cpSep
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
				"-allow-phantom-refs",
				"-no-bodies-for-excluded",
				"-exclude", "java",
				"-exclude", "javax",
				"-output-format", "none",
				"-p", "jb", "use-original-names:true",
				"-p", "cg.spark", "on",
				"-app", className } );
	}

	private ITestHandler<UpdatablePossibleType> ITestHandlerNewVersion() {
		return new DynamicTestHandler("pdfsam-2.2.0.jar", "pdfsam-2.2.1.jar", "pdfsam.jar") {
			
			@Override
			public void extendBasicTest
					(UpdatableInterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
						UpdatableInterproceduralCFG<Unit,SootMethod>> solver) {
				//
			}
			
			@Override
			public void performExtendedTest
					(UpdatableInterproceduralCFG<Unit, SootMethod> icfg,
					IFDSSolver<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>,
						UpdatableInterproceduralCFG<Unit,SootMethod>> solver,
					int phase) {
				//
			}
		};
	}
	
	/**
	 * Performs a simple analysis and then replaces the SweetHome application with a
	 * newer version
	 */
	@Test
	public void newVersionSH_Rerun() {
		System.out.println("Starting newVersionJU_Rerun...");
		performTestRerun(ITestHandlerNewVersion(), "org.pdfsam.guiclient.GuiClient");
		System.out.println("newVersionJU_Rerun finished.");
	}
	
	/**
	 * Performs a simple analysis and then replaces the SweetHome application with a
	 * newer version
	 */
	@Test
	public void newVersionSH_Propagate() {
		System.out.println("Starting newVersionJU_Propagate...");
		performTestDirect(ITestHandlerNewVersion(), "org.pdfsam.guiclient.GuiClient");
		System.out.println("newVersionJU_Propagate finished.");
	}

}
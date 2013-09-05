package soot.jimple.interproc.ifds.test;

import heros.IFDSTabulationProblem;
import heros.incremental.AbstractUpdatableInterproceduralCFG;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.incremental.UpdatableWrapper;
import heros.solver.IFDSSolver;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
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
import soot.jimple.toolkits.ide.exampleproblems.incremental.IFDSReachingDefinitions;
import soot.jimple.toolkits.ide.exampleproblems.incremental.UpdatableReachingDefinition;
import soot.jimple.toolkits.ide.icfg.UpdatableJimpleBasedInterproceduralCFG;

public class IFDSReachingDefinitionsSootCommits {

	private final static int TEST_COUNT = 10;
	private final static String JUNIT_DIR = "soot Versions";
	private final static String CLASS_NAME = "soot.Main";

	private void patchGraph() {
		final boolean AGGRESSIVE_CHECKS = true;
		
		// Get the original call graph size before we change anything
		System.out.println("Original call graph has " + Scene.v().getCallGraph().size() +  " edges");
			
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

		// Make sure that we load all class dependencies of the new version
		Scene.v().loadNecessaryClasses();

		// Reload all application classes
		List<SootClass> newClasses = new ArrayList<SootClass>();
		for (SootClass sc : allClasses) {
			// Force a new class resolving
			SootClass scNew;
			try {
				scNew = Scene.v().forceResolve(sc.getName(), SootClass.SIGNATURES);
			}
			catch (Exception ex) {
				// The class might have been removed
				System.err.println("Could not load class " + sc + ", skipping...");
				continue;
			}
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
		for (SootClass sc : Scene.v().getClasses())
			if (sc.resolvingLevel() < SootClass.SIGNATURES) {
				Scene.v().forceResolve(sc.getName(), SootClass.SIGNATURES);
				System.out.println("Reloaded class " + sc.getName());
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
		
	private Set<UpdatableReachingDefinition> computeUpdate(final String initialCodeDir,
			final String updatedCodeDir) {
//		extractVersion(initialCodeDir);

		final String codeDir = JUNIT_DIR + File.separator + "run";
		
		soot.G.reset();
		final Set<UpdatableReachingDefinition> results = new HashSet<UpdatableReachingDefinition>();

		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
				long timeBefore = System.nanoTime();
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				AbstractUpdatableInterproceduralCFG<Unit, SootMethod> icfg =
						new UpdatableJimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatableReachingDefinition, UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit, SootMethod>> problem =
						new IFDSReachingDefinitions(icfg);
				IFDSSolver<UpdatableWrapper<Unit>,UpdatableReachingDefinition,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>> solver =
						new IFDSSolver<UpdatableWrapper<Unit>,UpdatableReachingDefinition,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>>(problem);	
				
				long beforeSolver = System.nanoTime();
				System.out.println("Running solver...");
				solver.solve();
				System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");
				
				SootMethod meth = Scene.v().getMainClass().getMethodByName("main"); 
				UpdatableWrapper<Unit> ret = icfg.wrap(meth.getActiveBody().getUnits().getPredOf
						(meth.getActiveBody().getUnits().getLast()));
				
				long nanoBeforePatch = System.nanoTime();
				copyDirectory(updatedCodeDir + File.separator + "classes", codeDir);
				patchGraph();
				System.out.println("Graph patched in " + (System.nanoTime() - nanoBeforePatch) / 1E9 + " seconds.");
				
//				Scene.v().getSootClass(className).setApplicationClass();
						
				nanoBeforeCFG = System.nanoTime();
				icfg = new UpdatableJimpleBasedInterproceduralCFG((int) icfg.size());
				System.out.println("ICFG updated in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");
						
				long nanoBeforeUpdate = System.nanoTime();
				solver.update(icfg);
				System.out.println("IDE results updated in " + (System.nanoTime() - nanoBeforeUpdate) / 1E9 + " seconds.");						

				results.addAll(solver.ifdsResultsAt(ret));
//				solver.dumpResults(className + "_Propagate.csv");

				System.out.println("Time elapsed: " + ((double) (System.nanoTime() - timeBefore)) / 1E9);
			}
		}));
		
		copyDirectory(initialCodeDir + File.separator + "classes", codeDir);
		
		final String sootcp = codeDir + File.pathSeparator
				+ JUNIT_DIR + "/lib/hamcrest-core-1.3.jar" + File.pathSeparator
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
				"-allow-phantom-refs",
//				"-pp",
				"-no-bodies-for-excluded",
				"-exclude", "java",
				"-exclude", "javax",
				"-cp", sootcp,
				"-output-format", "none",
				"-p", "jb", "use-original-names:true",
				"-p", "cg.spark", "on",
//				"-p", "cg.spark", "verbose:true",
				CLASS_NAME } );
		return results;
	}

	private Set<UpdatableReachingDefinition> computeResults(final String codeDir) {
//		extractVersion(codeDir);
		
		soot.G.reset();
 		final Set<UpdatableReachingDefinition> results = new HashSet<UpdatableReachingDefinition>();
 
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
//				Scene.v().getSootClass(className).setApplicationClass();
				System.out.println("Running IFDS on initial CFG...");
				
				long nanoBeforeCFG = System.nanoTime();
				UpdatableInterproceduralCFG<Unit, SootMethod> icfg =
						new UpdatableJimpleBasedInterproceduralCFG();
				System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

				IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatableReachingDefinition, UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit, SootMethod>> problem =
					new IFDSReachingDefinitions(icfg);
				IFDSSolver<UpdatableWrapper<Unit>,UpdatableReachingDefinition,UpdatableWrapper<SootMethod>,
							UpdatableInterproceduralCFG<Unit,SootMethod>> solver =
					new IFDSSolver<UpdatableWrapper<Unit>,UpdatableReachingDefinition,UpdatableWrapper<SootMethod>,
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
			Set<UpdatableReachingDefinition> results = computeResults(JUNIT_DIR + File.separator
					+ updatedVersion);
			System.out.println(results);
			Set<UpdatableReachingDefinition> resultsNew = computeUpdate(JUNIT_DIR + File.separator
					+ initialVersion, JUNIT_DIR + File.separator + updatedVersion);
			System.out.println(resultsNew);
			
			Assert.assertEquals(results.size(), resultsNew.size());
			for (UpdatableReachingDefinition urdNew : resultsNew) {
				boolean found = false;
				for (UpdatableReachingDefinition urdOld : results)
					if (urdNew.getContents().toString().equals(urdOld.getContents().toString())) {
						found = true;
						break;
					}
				Assert.assertTrue("Results do not match, aborting...", found);
				if (!found)
					return false;
			}
		}
		return true;
	}
	
    private static void delete(File file) throws IOException{
       	if(file.isDirectory()){
       		//directory is empty, then delete it
       		if(file.list().length==0){
       		   file.delete();
       		   System.out.println("Directory is deleted : " + file.getAbsolutePath());
       		}
       		else{
       		   //list all the directory contents
           	   String files[] = file.list();
     
           	   for (String temp : files) {
           	      //construct the file structure
           	      File fileDelete = new File(file, temp);
     
           	      //recursive delete
           	     delete(fileDelete);
           	   }
     
           	   //check the directory again, if empty then delete it
           	   if(file.list().length==0){
              	     file.delete();
           	     System.out.println("Directory is deleted : " 
                                                     + file.getAbsolutePath());
           	   }
       		}
       	}
       	else{
       		//if file, then delete it
       		file.delete();
       		System.out.println("File is deleted : " + file.getAbsolutePath());
       	}
    }
    
    public static void copyFolder(File src, File dest) throws IOException{
    	if(src.isDirectory()){
    		//if directory not exists, create it
    		if(!dest.exists()){
    			dest.mkdir();
        		System.out.println("Directory copied from " + src + "  to " + dest);
    		}
     
        	//list all the directory contents
        	String files[] = src.list();
     
        	for (String file : files) {
        		//construct the src and dest file structure
        		File srcFile = new File(src, file);
        		File destFile = new File(dest, file);
        		//recursive copy
        		copyFolder(srcFile,destFile);
        	}
    	}
    	else{
    		//if file, then copy it
        	//Use bytes stream to support all file types
        	InputStream in = new FileInputStream(src);
        	OutputStream out = new FileOutputStream(dest); 
     
        	byte[] buffer = new byte[1024];
        	int length;
        	//copy the file content in bytes 
        	while ((length = in.read(buffer)) > 0){
        		out.write(buffer, 0, length);
        	}
     
        	in.close();
        	out.close();
        	System.out.println("File copied from " + src + " to " + dest);
        }
    }

	private void copyDirectory(String sourceDir, String targetDir) {
		try {
	    	delete(new File(targetDir));
	    	copyFolder(new File(sourceDir), new File(targetDir));
		}
		catch (IOException ex) {
			System.out.println("Could not copy folder: " + ex.getMessage());
		}
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
package soot.jimple.interproc.ifds.test;

import heros.util.Utils;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class VespucciCommitAggregator {

	private final static String VESPUCCI_DIR = "D:\\Arbeit\\Inkrementelle Analyse\\vespucci_developer-changes";
	private final static String VESPUCCI_OUT = "D:\\Arbeit\\Inkrementelle Analyse\\vespucci_versions";
	
	/**
	 * @param args
	 * @throws IOException 
	 */
	public static void main(String[] args) throws IOException {
		Set<String> commitIds = collectCommitIDs(new File(VESPUCCI_DIR));
		List<String> orderedCommits = new ArrayList<String>(commitIds);
		Collections.sort(orderedCommits);
		System.out.println("Found the following commit sets: " + orderedCommits);
		
		if (orderedCommits.isEmpty())
			return;
		
		// For every commit set, create a version of Vespucci
		while (!orderedCommits.isEmpty()) {
			String commitId = orderedCommits.remove(0);
			File outDir = buildOutDir(commitId);
			System.out.println("Generating version " + commitId + "...");
			generateVespucciVersion(new File(VESPUCCI_DIR), outDir, Long.parseLong(commitId));
		}
	}

	private static void generateVespucciVersion(File inDir, File outDir, long commitId) throws IOException {
		if (!outDir.exists())
			outDir.mkdir();
		
		Set<String> classFiles = new HashSet<String>();
		for (File subFile : inDir.listFiles()) {
			if (subFile.isDirectory())
				generateVespucciVersion(subFile, new File(outDir.getAbsolutePath()
						+ File.separator + subFile.getName()), commitId);
			else if (subFile.getName().endsWith(".class")) {
				String fileName = subFile.getName();
				fileName = fileName.substring(fileName.indexOf("_") + 1);
				fileName = fileName.substring(fileName.indexOf("_") + 1);
				classFiles.add(fileName);
			}
		}
		
		for (String classFile : classFiles) {
			long closestMatch = -1;
			File closestFile = null;
			for (File subFile : inDir.listFiles())
				if (!subFile.isDirectory())
					if (subFile.getName().endsWith("_" + classFile)) {
						Long cid = Long.parseLong(subFile.getName().substring(0, subFile.getName().indexOf("_")));
						if (cid == commitId) {
							Utils.copyFile(subFile.getAbsolutePath(), outDir + File.separator + classFile);
							break;
						}
						else if (cid < commitId && cid > closestMatch) {
							closestMatch = cid;
							closestFile = subFile;
						}
					}
			if (closestMatch >= 0)
				Utils.copyFile(closestFile.getAbsolutePath(), outDir + File.separator + classFile);
		}
	}

	private static File buildOutDir(String commitID) {
		File parentDir = new File(VESPUCCI_OUT + File.separatorChar + commitID);
		if (!parentDir.exists())
			parentDir.mkdir();
		return parentDir;
	}

	private static Set<String> collectCommitIDs(File baseDir) {
		Set<String> commitIDs = new HashSet<String>();
		for (File subFile : baseDir.listFiles()) {
			if (subFile.isDirectory())
				commitIDs.addAll(collectCommitIDs(subFile));
			else if (subFile.getName().endsWith(".class"))
				commitIDs.add(subFile.getName().substring(0, subFile.getName().indexOf("_")));
		}
		return commitIDs;
	}

}

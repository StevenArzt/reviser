package soot.jimple.interproc.ifds.test;

import org.junit.runner.JUnitCore;
import org.junit.runner.Request;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;

public class SingleJUnitTestRunner { 
    public static void main(String... args) throws ClassNotFoundException { 
        String[] classAndMethod = args[0].split("#"); 
        Request request = Request.method(Class.forName(classAndMethod[0]), 
                classAndMethod[1]); 
 
        Result result = new JUnitCore().run(request);
        if (result.wasSuccessful())
        	System.out.println("Test run was successful");
        else {
        	System.out.println("Test run was NOT successful: ");
        	for (Failure f : result.getFailures())
        		System.out.println(f.getMessage() + " - Trace: " + f.getTrace() + " - Exception: "
        				+ f.getException() + " - " + f.getException().getStackTrace());
        }
        System.exit(result.wasSuccessful() ? 0 : 1); 
    } 
} 

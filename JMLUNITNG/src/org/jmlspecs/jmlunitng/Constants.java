

package org.jmlspecs.jmlunitng;

/**
 * An interface for defining constants.
 *
 * @author Rinkesh Nagmoti
 * @version 
 */
public interface Constants extends org.multijava.mjc.Constants {

    String TEST_CLASS_NAME_POSTFIX = "_JML_Test";
    String TEST_CLASS_FILE_NAME_POSTFIX = "_JML_Test.java";
    String TEST_DATA_NAME_POSTFIX = "_JML_TestData";
    String TEST_DATA_FILE_NAME_POSTFIX = "_JML_TestData.java";
    String TEST_METHOD_NAME_PREFIX = "test";
    String DOT_JAVA = ".java";
    
    // The following constants are prepended to simple class names
    // appearing in the generated code to build qualified names.
    // If non-empty, they need a "." at the end!

    /** The name of the JUnit framework package. */
    String PKG_JUNIT = "junit.framework.";
    /** The name of the JML RAC runtime package. */
    String PKG_JMLRAC = "org.jmlspecs.jmlrac.runtime.";
    /** The name of the JML jmlunit package. */
    String PKG_JMLUNITNG = "org.jmlspecs.jmlunitng.";
    /** The name of the JML jmlunit strategies package. */
    String PKG_STRATEGIES = "org.jmlspecs.jmlunit.strategies.";

    /*@ invariant PKG_JUNIT.length() > 0
      @       ==> PKG_JUNIT.charAt(PKG_JUNIT.length()) == '.';
      @*/
    /*@ invariant PKG_JMLRAC.length() > 0
      @       ==> PKG_JMLRAC.charAt(PKG_JMLRAC.length()) == '.';
      @*/
    /*@ invariant PKG_JMLUNITNG.length() > 0
      @       ==> PKG_JMLUNITNG.charAt(PKG_JMLUNIT.length()) == '.';
      @*/
    /*@ invariant PKG_STRATEGIES.length() > 0
      @       ==> PKG_STRATEGIES.charAt(PKG_JMLUNIT.length()) == '.';
      @*/
}

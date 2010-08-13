/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.testng;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;

import org.testng.ITestResult;
import org.testng.TestListenerAdapter;
/**
 * A listener used by TestNG to gather basic data about test runs.
 * @author Jonathan Hogins
 * @version April 2010
 */
public class BasicTestListener extends TestListenerAdapter {
  /**
   * The newline string.
   */
  private static final String NEWLINE = System.getProperty("line.separator");

  /**
   * The writer to use for output.
   */
  private Writer my_writer;

  // constraint
  // "When a test status is reported, the name of the method being tested and\
  // \ parameter information is reported to disk with the status."
  /**
   * Creates a new BasicTestListener that sends test results to the given
   * writer.
   * 
   * @param the_writer The writer for which to send.err.ut.
   */
  // @ ensures my_writer == the_writer
  public BasicTestListener(final Writer the_writer) {
    my_writer = the_writer;
  }

  /**
   * Creates a new BasicTestListener that sends text results to standard output.
   */
  public BasicTestListener() {
    this(new OutputStreamWriter(System.out));  
  }
  
  /**
   * Writes test success info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public void onTestSuccess(final ITestResult the_tr) {
    try {
      my_writer.write("Passed: ");
      my_writer.write(testString(the_tr));
      my_writer.write(NEWLINE);
      super.onTestSuccess(the_tr);
      my_writer.flush();
    } catch (final IOException e) {
      System.err.println("Could not write to supplied Writer in BasicTestListener.");
      e.printStackTrace();
    }
  }

  /**
   * Writes test failure info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public void onTestFailure(final ITestResult the_tr) {
    try {
      my_writer.write("Failed: ");
      my_writer.write(testString(the_tr));
      my_writer.write(NEWLINE);
      super.onTestFailure(the_tr);
      my_writer.flush();
    } catch (final IOException e) {
      System.err.println("onTestFailure: Could not write to supplied Writer " +
        "in BasicTestListener.");
      e.printStackTrace();
    }
  }

  /**
   * Writes test skipped info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public void onTestSkipped(final ITestResult the_tr) {
    try {
      my_writer.write("Skipped: ");
      my_writer.write(testString(the_tr));
      my_writer.write(NEWLINE);
      super.onTestSkipped(the_tr);
      my_writer.flush();
    } catch (final IOException e) {
      System.err.println("onTestSkipped: Could not write to supplied Writer " +
        "in BasicTestListener.");
      e.printStackTrace();
    }
  }

  /**
   * Writes test failed but within success percentage info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public void onTestFailedButWithinSuccessPercentage(final ITestResult the_tr) {
    try {
      my_writer.write("Test Failed, but was within success percentage\n");
      my_writer.write(testString(the_tr));
      my_writer.write("   " + the_tr.getThrowable());
      my_writer.write(NEWLINE);
      super.onTestFailedButWithinSuccessPercentage(the_tr);
      my_writer.flush();
    } catch (final IOException e) {
      System.err.println("onTestFailedButWithinSuccessPercentage: Could not write " + 
        "to supplied Writer in BasicTestListener.");
      e.printStackTrace();
    }
  }

  /**
   * @param the_test_result A test result.
   * @return a String describing the test that was run to generate
   * the result.
   */
  private final String testString(final ITestResult the_test_result) {
    final StringBuilder sb = new StringBuilder();
    final String trunc_name = 
      the_test_result.getMethod().getMethodName().replace("test_", "");
    final Object[] params = the_test_result.getParameters();
    int start_index = 0;
    
    String class_name = the_test_result.getTestClass().getName();
    class_name = class_name.substring(class_name.lastIndexOf('.') + 1);
    
    if (class_name.startsWith(trunc_name + "_JML_Test")) {
      // this is a constructor test, so there is no object to print and
      // we have to print parameter 0, if any, as the first parameter
      sb.append("Constructor " + trunc_name + "(");
    }
    else {
      // this is a regular method test, so we have to print the object
      sb.append("<<" + params[0] + ">>." + trunc_name + "(");
      start_index = 1;
    }
    for (int i = start_index; i < params.length - 1; i++) {
      sb.append(params[i] + ", ");
    }
    if (params.length > 1) {
      sb.append(String.valueOf(params[params.length - 1]));
    }
    sb.append(")");
    
    return sb.toString();
  }
}

/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.testng;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;

import org.testng.ITestContext;
import org.testng.ITestListener;
import org.testng.ITestResult;

/**
 * A listener used by TestNG to gather basic data about test runs.
 * 
 * @author Daniel M. Zimmerman
 * @version November 2010
 */
public class BasicTestListener implements ITestListener {
  /**
   * The newline string.
   */
  private static final String NEWLINE = System.getProperty("line.separator");

  /**
   * The test prefix.
   */
  private static final String TEST_PREFIX = "test_";
  
  /**
   * The test parameter separator.
   */
  private static final String TEST_PARAM_SEPARATOR = "__";
  
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
  
  @Override
  public void onTestStart(final ITestResult result) {
    // do nothing
  }

  @Override
  public void onStart(final ITestContext context) {
    // do nothing
  }

  @Override
  public void onFinish(final ITestContext context) {
    // do nothing
  }
  
  /**
   * Writes test success info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public synchronized void onTestSuccess(final ITestResult the_tr) {
    try {
      my_writer.write("Passed: ");
      my_writer.write(testString(the_tr));
      my_writer.write(NEWLINE);
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
  public synchronized void onTestFailure(final ITestResult the_tr) {
    try {
      my_writer.write("Failed: ");
      my_writer.write(testString(the_tr));
      my_writer.write(NEWLINE);
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
  public synchronized void onTestSkipped(final ITestResult the_tr) {
    try {
      my_writer.write("Skipped: ");
      my_writer.write(testString(the_tr));
      my_writer.write(NEWLINE);
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
  public synchronized void onTestFailedButWithinSuccessPercentage(final ITestResult the_tr) {
    try {
      my_writer.write("Failed Within Success Percentage: ");
      my_writer.write(testString(the_tr));
      my_writer.write("   " + the_tr.getThrowable());
      my_writer.write(NEWLINE);
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
    final String trunc_name = getOriginalMethodName(the_test_result);
    final Object[] params = the_test_result.getParameters();
    int start_index = 0;
    
    String class_name = the_test_result.getTestClass().getName();
    class_name = class_name.substring(class_name.lastIndexOf('.') + 1);
    
    if (class_name.startsWith(trunc_name + "_JML_Test")) {
      // this is a constructor test, so there is no object to print and
      // we have to print parameter 0, if any, as the first parameter
      sb.append("Constructor " + trunc_name + "(");
    }
    else if (params.length == 0) {
      sb.append(trunc_name + "(");
    }
    else if (params.length > 0) {
      // this is a regular method test, so we have to print the object
      sb.append("<<" + params[0] + ">>." + trunc_name + "(");
      start_index = 1;
    }
    for (int i = start_index; i < params.length - 1; i++) {
      sb.append(params[i] + ", ");
    }
    if (params.length > 1) {
      sb.append(params[params.length - 1]);
    }
    sb.append(")");
    
    return sb.toString();
  }
  
  /**
   * @param the_test_result A test result.
   * @return the original name of the method being tested, as a String.
   */
  private final String getOriginalMethodName
  (final ITestResult the_test_result) {
    // if the method name contains the String TEST_PARAM_SEPARATOR, and the test had
    // more than one parameter, we extended the method name; otherwise
    // it was a no-parameter method name that we left alone
    String orig_name = the_test_result.getName();
    
    if (orig_name.startsWith(TEST_PREFIX)) {
      orig_name = orig_name.substring(TEST_PREFIX.length());
    }
    if (orig_name.contains(TEST_PARAM_SEPARATOR) && 
        the_test_result.getParameters().length > 0) {
      // find the first occurrence of TEST_PARAM_SEPARATOR, and remove it and everything
      // that follows
      orig_name = orig_name.substring(0, orig_name.indexOf(TEST_PARAM_SEPARATOR));
    }
    
    return orig_name;
  }
}

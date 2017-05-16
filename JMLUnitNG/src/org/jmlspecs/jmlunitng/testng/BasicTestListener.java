/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.testng;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.lang.reflect.Array;

import org.testng.ITestContext;
import org.testng.ITestListener;
import org.testng.ITestResult;

/**
 * A listener used by TestNG to gather basic data about test runs.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
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
   * The static prefix.
   */
  private static final String STATIC_PREFIX = "static_";
  
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
   * @param the_writer The writer to use for streaming test results.
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
  public void onTestStart(final ITestResult the_result) {
    // do nothing
  }

  @Override
  public void onStart(final ITestContext the_context) {
    // do nothing
  }

  @Override
  public void onFinish(final ITestContext the_context) {
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
      System.err.println("onTestFailure: Could not write to " +
                         "supplied Writer in BasicTestListener.");
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
  private String testString(final ITestResult the_test_result) {
    final StringBuilder sb = new StringBuilder();
    final String trunc_name = getOriginalMethodName(the_test_result);
    final Object[] params = the_test_result.getParameters();
    int start_index = 0;
    
    String class_name = the_test_result.getTestClass().getName();
    if (class_name.contains(".")) {
      class_name = class_name.substring(class_name.lastIndexOf('.') + 1);
    }
    
    if (class_name.startsWith(trunc_name + "_JML_Test")) {
      // this is a constructor test, so there is no object to print and
      // we have to print parameter 0, if any, as the first parameter
      sb.append("constructor " + trunc_name + '(');
    } else if (params.length == 0) {
      if (isStaticTest(the_test_result)) {
        // print that it's a static method
        sb.append("static ");
      }
      sb.append(trunc_name + '(');
    } else if (params.length > 0) {
      if (isStaticTest(the_test_result)) {
        // print that it's a static method
        sb.append("static ");
      } else {
        // this is a regular method test, so we have to print the object
        sb.append("<<" + params[0] + ">>.");        
        start_index = 1;
      }
      sb.append(trunc_name + '(');
    }
    for (int i = start_index; i < params.length - 1; i++) {
      sb.append(formatParameter(params[i]) + ", ");
    }
    if (params.length > 1 || (start_index == 0 && params.length == 1)) {
      sb.append(formatParameter(params[params.length - 1]));
    }
    sb.append(")");
    
    return sb.toString();
  }
  
  /**
   * @param the_test_result A test result.
   * @return the original name of the method being tested, as a String.
   */
  private String getOriginalMethodName(final ITestResult the_test_result) {
    // if the method name contains the String TEST_PARAM_SEPARATOR, and the test had
    // more than one parameter, we extended the method name; otherwise
    // it was a no-parameter method name that we left alone
    String orig_name = the_test_result.getName();
    if (orig_name.startsWith(TEST_PREFIX)) {
      orig_name = orig_name.substring(TEST_PREFIX.length());
    }
    if (orig_name.startsWith(STATIC_PREFIX)) {
      orig_name = orig_name.substring(STATIC_PREFIX.length());
    }
    if (orig_name.contains(TEST_PARAM_SEPARATOR)) {
      // find the first occurrence of TEST_PARAM_SEPARATOR, and remove it and everything
      // that follows
      orig_name = orig_name.substring(0, orig_name.indexOf(TEST_PARAM_SEPARATOR));
    }
    return orig_name;
  }
  
  /**
   * @param the_test_result The test result.
   * @return true if the_test_result is a result for a static method, false
   * otherwise.
   */
  private boolean isStaticTest(final ITestResult the_test_result) {
    return the_test_result.getName().startsWith(TEST_PREFIX + STATIC_PREFIX);
  }
  
  /**
   * @param the_parameter The parameter to format.
   * @return a formatted version of the parameter, including displaying
   * the contents of arrays.
   */
  private String formatParameter(final Object the_parameter) {
    String result = "null";
    if (the_parameter != null) {
      result = the_parameter.toString();
      if (the_parameter.getClass().isArray()) {
        final StringBuilder sb = new StringBuilder();
        final int length = Array.getLength(the_parameter);
        sb.append('{');
        for (int i = 0; i < length - 1; i++) {
          sb.append(formatParameter(Array.get(the_parameter, i)));
          sb.append(", ");
        }
        if (length > 0) {
          sb.append(formatParameter(Array.get(the_parameter, length - 1)));
        }
        sb.append('}');
        result = sb.toString();
      }
    }
    
    return result;
  }
}

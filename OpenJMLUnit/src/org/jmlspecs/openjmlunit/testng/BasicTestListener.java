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

package org.jmlspecs.openjmlunit.testng;

import java.io.IOException;
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
   * The writer to use for.err.ut.
   */
  private Writer my_writer;

  // constraint
  // "When a test status is reported, the name of the method being tested and\
  // \ parameter information is reported to disk with the status."
  /**
   * Creates a new BasicTestListener that sends test result.err.ut to the given
   * writer.
   * 
   * @param the_writer The writer for which to send.err.ut.
   */
  // @ ensures my_writer == the_writer
  public BasicTestListener(final Writer the_writer) {
    my_writer = the_writer;
  }

  /**
   * Writes test success info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public void onTestSuccess(final ITestResult the_tr) {
    try {
      my_writer.write("Test Success.\n");
      my_writer.write(the_tr.toString());
      my_writer.write(NEWLINE);
      super.onTestSuccess(the_tr);
      my_writer.flush();
    } catch (final IOException e) {
      System.err.println("Could not write to supplied Writer in BasicTestListener.");
      e.printStackTrace();
    }
  }

  /**
   * Writes test success info to my_writer.
   * 
   * @param the_tr The test result info.
   */
  public void onTestFailure(final ITestResult the_tr) {
    try {
      my_writer.write("Test Failed\n");
      my_writer.write(the_tr.toString());
      my_writer.write("   " + the_tr.getThrowable());
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
      my_writer.write("Test Skipped\n");
      my_writer.write(the_tr.toString());
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
      my_writer.write(the_tr.toString());
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

}

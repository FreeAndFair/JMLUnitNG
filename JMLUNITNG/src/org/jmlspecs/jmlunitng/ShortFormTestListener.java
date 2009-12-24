
package org.jmlspecs.jmlunitng;

import org.testng.TestListenerAdapter;
import org.testng.ITestResult;

/**
 * An abbreviated test listener.
 */
public class ShortFormTestListener extends TestListenerAdapter {
  private int m_count = 0;
 
  @Override
  public void onTestFailure(ITestResult tr) {
    log("F");
  }
 
  @Override
  public void onTestSkipped(ITestResult tr) {
    log("S");
  }
 
  @Override
  public void onTestSuccess(ITestResult tr) {
    log(".");
  }
 
  private void log(String string) {
    System.out.print(string);
    if (m_count % 40 == 0) {
      System.out.println("");
    }
    if (m_count % 100000 == 0) {
      System.out.println("\n" + m_count + " tests completed" + "\n");
    }
    m_count++;
  }
}

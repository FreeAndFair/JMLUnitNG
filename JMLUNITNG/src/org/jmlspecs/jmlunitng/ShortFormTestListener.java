
package org.jmlspecs.jmlunitng;

import org.testng.TestListenerAdapter;
import org.testng.ITestResult;

/**
 * An abbreviated test listener.
 */
public class ShortFormTestListener extends TestListenerAdapter {
  private int m_count = 0;
  private int failures = 0;
  private int skips = 0;
  
  private final long startTime = System.currentTimeMillis();
  
  @Override
  public void onTestFailure(ITestResult tr) {
    failures++;
    log("F");
  }
 
  @Override
  public void onTestSkipped(ITestResult tr) {
    skips++;
    log("S");
  }
 
  @Override
  public void onTestSuccess(ITestResult tr) {
    log(".");
  }
 
  private synchronized void log(String string) {
    boolean new_line = m_count++ % 40 == 0;
    
    if ((m_count - 1) % 100000 == 0 && m_count != 1) {
      System.out.println("\n" + (m_count - 1) + "/" + skips + "/" + failures + " " +
                         "tests/skips/fails" + ", elapsed time " +
                         (System.currentTimeMillis() - startTime) / 1000 + "s" + "\n");
    }
    else if (new_line) {
      System.out.println("");
    }
    System.out.print(string);
  }
}


package org.jmlspecs.jmlunitng;

import org.testng.TestNG;

/**
 * Runs the test.
 * 
 * @version 1.0
 * @author Rinkesh Nagmoti.
 * */
public class TestRunner extends TestNG
{

  /**
   * Runs the tests specified in the given class.
   * 
   * @param the_classes Array of Class objects.
   */
  public void runTests(final Class[] the_classes)
  {
    super.setTestClasses(the_classes);
    super.run();
  }
}


package org.jmlspecs.jmlunitng;

import org.testng.TestNG;

/** Runs the test. */
public class TestRunner extends TestNG
{
 /**
  * Constructs the test runner object.
  */
  public TestRunner ()
  {
    
  }
  public void runTests(Class[] the_classes)
  {
    super.setTestClasses(the_classes);
    super.run();
  }
}

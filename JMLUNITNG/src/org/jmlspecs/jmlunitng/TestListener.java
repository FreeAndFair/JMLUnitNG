package org.jmlspecs.jmlunitng;
import org.testng.TestListenerAdapter;
import org.testng.ITestResult;




/**
 *  This is the test listener.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class TestListener extends TestListenerAdapter implements Constants
{


  /**
   * This method get executed when the test is failed to execute.
   * @param the_tr ITestResult object.
   */
  @Override
  public void onTestFailure(final ITestResult the_tr)
  {
    final Object[] parameters = the_tr.getParameters();
   
    final StringBuilder message = new StringBuilder();
    message.append("Failed test : " + the_tr.getMethod().getMethodName() + BKT_ST);
   // message.append("Object used is : " + parameters[0] + "  and parameters used are : ");
    for (int i = 1; i < parameters.length; i++)
    {
      message.append(parameters[i]);
      
      if (i <  parameters.length - 1)
      {
        message.append("," + " ");
      }
    }
    message.append(")  for object " + parameters[0] + " \n");
    log(message.toString());
  }

 
  /**
   * This method get executed when the test is skipped.
   * @param the_tr ITestResult object.
   */
  @Override
  public void onTestSkipped(final ITestResult the_tr)
  {
    final Object[] parameters = the_tr.getParameters();
   
    final StringBuilder message = new StringBuilder();
    message.append("Skipped test : " + the_tr.getMethod().getMethodName() + "(");
   // message.append("Object used is : " + parameters[0] + "  and parameters used are : ");
    for (int i = 1; i < parameters.length; i++)
    {
      message.append(parameters[i]);
      
      if (i <  parameters.length - 1)
      {
        message.append(", ");
      }
    }
    message.append(")" + "  for object " + parameters[0] + "\n");
    log(message.toString());
  }


  /**
   * This method get executed when the test is successful.
   * @param the_tr ITestResult object.
   */
  @Override
  public void onTestSuccess(final ITestResult the_tr)
  {
   // log(".");
  }
/**
 * This method logs the details.
 * @param the_string log message.
 */
  private void log(final String the_string) 
  {
 
    System.out.print(the_string);
 
  }

}

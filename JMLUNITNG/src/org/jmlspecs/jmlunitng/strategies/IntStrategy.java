package org.jmlspecs.jmlunitng.strategies;
/**
 * This is the strategy to handle basic data of type int.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class IntStrategy extends AbstractBasicStrategy
{
  /**
   * This method provides the user input data 
   * and need to be overridden in the test data class. 
   * @return Object[]
   */
  @Override
  public Object[] addData()
  {
   
    return new Object[]{};
  }
/**
 * This method provides the default data.
 * @return Object[]
 */
  @Override
  public Object[] defaultData()
  {
    return new Integer[]{-1, 0, 1, };
  }

}

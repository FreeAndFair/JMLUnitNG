package org.jmlspecs.jmlunitng.strategies;
/**
 *  This class provides the strategy to generate the iterator 
 *  to provide data of type Boolean.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class BooleanStrategy extends AbstractBasicStrategy
{
  /**
   * This method provides the user input data 
   * and need to be overridden in the test data class. 
   * @return Object[]
   */
  @Override
  public Object[] addData()
  {
   
    return new Boolean[]{};
  }
/**
 * This method provides the default data.
 * @return Object[]
 */
  @Override
  public Object[] defaultData()
  {
    return new Boolean[]{false, true, };
  }
  /**
   * This method provides the user data for all boolean strategies.
   * @return Object[]
   */
  @Override
  public Object[] addDataForAll()
  {
   
    return new Boolean[]{};
  }
}

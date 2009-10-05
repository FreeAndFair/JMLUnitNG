
package org.jmlspecs.jmlunitng.strategies;

/**
 * This class provides the strategy to generate the iterator to provide data of
 * type String.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class StringStrategy extends AbstractBasicStrategy
{
  /**
   * This method provides the user input data and need to be overridden in the
   * test data class.
   * 
   * @return Object[]
   */
  @Override
  public Object[] addData()
  {

    return new Object[] {};
  }

  /**
   * This method provides the default data.
   * 
   * @return Object[]
   */
  @Override
  public Object[] defaultData()
  {
    return new String[] {null, "", };
  }

  /**
   * This method provides the user data for all string strategies.
   * 
   * @return Object[]
   */
  @Override
  public Object[] addDataForAll()
  {

    return new String[] {};
  }
}

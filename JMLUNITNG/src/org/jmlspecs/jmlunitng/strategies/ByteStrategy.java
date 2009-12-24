
package org.jmlspecs.jmlunitng.strategies;

/**
 * This is the strategy to handle basic data of type byte.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class ByteStrategy extends AbstractBasicStrategy
{
  /**
   * This method provides the user input data and need to be overridden in the
   * test data class.
   * 
   * @return Object[]
   */
  @Override
  public StrategyIterator addData()
  {

    return new ParameterIterator(new Byte[]{});
  }

  /**
   * This method provides the default data.
   * 
   * @return Object[]
   */
  @Override
  public StrategyIterator defaultData()
  {
    return new ParameterIterator(new Byte[]{-1, 0, 1});
  }

  /**
   * This method provides the user data for all Integer strategies.
   * 
   * @return Object[]
   */
  @Override
  public StrategyIterator addDataForAll()
  {

    return new ParameterIterator(new Byte[]{});
  }

}

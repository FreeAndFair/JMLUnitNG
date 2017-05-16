
package org.jmlspecs.jmlunitng.strategies;

/**
 * This class provides the strategy to generate the iterator to provide data of
 * type long.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class LongStrategy extends AbstractBasicStrategy
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

    return new ParameterIterator(new Long[]{});
  }

  /**
   * This method provides the default data.
   * 
   * @return Object[]
   */
  @Override
  public StrategyIterator defaultData()
  {
    return new ParameterIterator(new Long[]{-1L, 0L, 1L});
  }

  /**
   * This method provides the user data for all Long strategies.
   * 
   * @return Object[]
   */
  @Override
  public StrategyIterator addDataForAll()
  {

    return new ParameterIterator(new Long[]{});
  }
}

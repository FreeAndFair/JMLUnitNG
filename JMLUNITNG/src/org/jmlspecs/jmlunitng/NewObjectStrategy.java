package org.jmlspecs.jmlunitng;

import org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy;

/**
 *  This is the class for generating iterator for non primitive objects.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class NewObjectStrategy extends ImmutableObjectAbstractStrategy
{

  /**
   * This method provides the default data for iterator.
   * @return Object[]
   */
  protected Object[] defaultData()
  {
    return new Object[] {null};
  }

}

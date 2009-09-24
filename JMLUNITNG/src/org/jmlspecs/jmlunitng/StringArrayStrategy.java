
package org.jmlspecs.jmlunitng;

import org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy;

/**
 * This class provides the iterator strategy for String Array.
 * 
 * @author Rinkesh Nagmoti.
 * @version 1.0
 */
// This method uses the old jmlunit strategies class
// ImmutableObjectAbstractStrategy
// to generate iterator.
public class StringArrayStrategy extends ImmutableObjectAbstractStrategy
{
  /**
   * This method provides the default data for iterator.
   * 
   * @return Object[]
   */
  protected Object[] defaultData()
  {
    return new String[][] {null, {"", ""},};
  }
}

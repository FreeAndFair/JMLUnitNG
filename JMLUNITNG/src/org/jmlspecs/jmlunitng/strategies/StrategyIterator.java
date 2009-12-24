
package org.jmlspecs.jmlunitng.strategies;

public interface StrategyIterator
{

  /**
   * This method provides current element in the iterator.
   * 
   * @return Object
   */
  Object get();

  /**
   * This method returns the boolean value if the iterator is at the last
   * element.
   * 
   * @return boolean
   */
  boolean atEnd();

  /**
   * This method advances an iterator to the next location.
   */
  void advance();

}

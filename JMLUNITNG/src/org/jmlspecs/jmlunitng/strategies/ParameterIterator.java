
package org.jmlspecs.jmlunitng.strategies;

/**
 * This Class is the basic iterator for all data types.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class ParameterIterator implements StrategyIterator
{
  /**
   * This int signifies current element.
   */
  private transient int my_current;
  
  /**
   * This is the array of objects to iterate.
   */
  private final transient Object[] my_objs;

  /**
   * This is the constructor for this class.
   * 
   * @param the_data Object[].
   */
  public ParameterIterator(final Object[] the_data)
  {
    my_current = 0;
    my_objs = the_data.clone();
  }

  /**
   * This method provides current element in the iterator.
   * 
   * @return Object
   */
  public Object get()
  {
    if (!atEnd())
    {
      return my_objs[my_current];
    }
    else
    {
      throw new IllegalArgumentException("invalid call");
    }
  }

  /**
   * This method returns the boolean value if the iterator is at the last
   * element.
   * 
   * @return boolean
   */
  public boolean atEnd()
  {
    return my_objs.length <= my_current;
  }

  /**
   * This method advances an iterator to the next location.
   */
  public void advance()
  {
    if (my_current < my_objs.length)
    {
      my_current = my_current + 1;
    }
    else
    {
      throw new IllegalArgumentException("invalid call");
    }
  }
}

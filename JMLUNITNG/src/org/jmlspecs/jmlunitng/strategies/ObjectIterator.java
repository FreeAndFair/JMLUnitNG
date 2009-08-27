package org.jmlspecs.jmlunitng.strategies;
/**
 *  This Class is the basic iterator for all data types.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class ObjectIterator
{
  /**
   * This int signifies current element.
   */
  private transient int my_current;
  /**
   * This int signifies max element.
   */
  private final transient int my_max;
  /**
   * This boolean signifies if the iterator is at the last element.
   */
  private transient boolean my_end;
  /**
   * This is the array of objects to iterate.
   */
  private final transient Object[] my_objs;
  /**
   * This is the constructor for this class. 
   * @param the_data Object[].
   */
  public ObjectIterator(final Object[] the_data)
  {
    my_current = 0;
    my_max = the_data.length;
    my_objs = the_data;
    my_end = false;
    
  }
  /**
   * This method provides current element in the iterator.
   * @return Object
   */
  public Object get()
  {
    return my_objs[my_current];
  }
  /**
   * This method returns the boolean value if the iterator is at the last element.
   * @return boolean 
   */
  public boolean atEnd()
  {
    if (my_current == (my_max - 1))
    {
      my_end = true;
    }
    else
    {
      my_end = false;
    }
    return my_end;
  }
  /**
   * This method advances an iterator to the next location.
   */
  public void advamce()
  {
    if (my_current < (my_max - 1))
    {
      my_current++;
    }
  }
}

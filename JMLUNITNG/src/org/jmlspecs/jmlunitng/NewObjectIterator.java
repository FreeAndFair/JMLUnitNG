package org.jmlspecs.jmlunitng;

import org.jmlspecs.jmlunit.strategies.NewObjectAbstractIterator;

/**
 * This class provides an iterator for new objects of non primitive data types.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class NewObjectIterator extends NewObjectAbstractIterator

{
  /**
   * This is the number of objects to be created.
   */
  private transient int my_num_objects;
  /**
   * This integer represents the current element in the iterator.
   */
  private transient int my_curr_object;
  /**
   * This is the boolean representing if the iterator reached last element or not.
   */
  private transient boolean my_at_end;
  
  /**
   * This is the constructor.
   */
  public NewObjectIterator()
  {
    super();
    my_num_objects = 0;
    my_curr_object = 0;
    my_at_end = false;
  }
  
  /**
   * This method advances the iterator.
   */
  @Override
  public void advance()
  {
    if (!my_at_end)
    {
      my_curr_object++;
      if (my_curr_object == my_num_objects)
      {
        my_at_end = true;
      }
    }
    
  }
  /**
   * This method checks if the iterator reached the last element or not.
   * @return boolean
   */
  @Override
  public boolean atEnd()
  {
    
    return my_at_end;
  }
  /**
   * This method provides the current object in the iterator.
   * @return Object
   */
  @Override
  public Object get()
  {
    
    return make(my_curr_object);
  }
/**
 * This method create the objects specified by user.
 * @return Object.
 * @param the_num int.
 */
  @Override
  public Object make(final int the_num)
  {
    return null;
  }
/**
 * This method provides the number of objects to be provided.
 * @param the_num int.
 */
  public void setNumObjects(final int the_num)
  {
    my_num_objects = the_num;
  }
}

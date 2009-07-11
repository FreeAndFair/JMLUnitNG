package org.jmlspecs.jmlunitng;

import java.util.Iterator;

/**
 * This class provides functionality to combine the CombinedParameterIterator
 * with object Iterator.
 * @author Rinkesh Nagmoti.
 * @version 1.0
 */
public class CombinedObjectParameterIterator
{

  /**
   *  This is the combined parameter iterator.
   */
  
  private Iterator<Object[]> my_param_Iter;
  /**
   * This is the object iterator.
   */
  private Iterator<Object> my_obj_Iter;
  /**
   *  This is the current object.
   */
  private Object my_currentObj;
  /**
   * This is the current parameters array.
   */
  private Object[] my_currentParams;
  
  /**
   *  This is the Iterator for reassignment.
   */
  private Iterator<Object[]> my_paramReassign;
  /**
   * Constructs the object of CombinedObjectParameterIterator.
   */
  public CombinedObjectParameterIterator(final Iterator<Object[]> the_paraIter,
                                         final Iterator<Object> the_objIter)
  {
    my_param_Iter = the_paraIter;
    my_obj_Iter = the_objIter;
    
  }
  
  /**
   * This method returns true if any of the iterators has the next element.
   * @return boolean.
   */
  public boolean hasNext()
  {
    if (my_param_Iter.hasNext() || my_obj_Iter.hasNext())
    {
      return true;
    }
    else
    {
      return false;
    }
  }
  
  /**
   * This method returns the next element as an array of object and parameters.
   */
  public Object[] next()
  {
    if(my_param_Iter.hasNext() ||  my_obj_Iter.hasNext())
    {
      if(my_currentObj == null)
      {
        my_currentObj = my_obj_Iter.next();
        my_currentParams = my_param_Iter.next();
        Object[] newArray = new Object[my_currentParams.length + 1];
        for (int i = 1; i < my_param_Iter.next().length + 1; i++)
        {
          newArray[i] = my_currentParams[i];
        }
        newArray[0] = my_currentObj;
        
        return newArray;
      }
      
      if(!my_param_Iter.hasNext())
      {
        if(my_obj_Iter.hasNext())
        {
          my_currentObj= my_obj_Iter.next();
          my_param_Iter = my_paramReassign;
          my_currentParams = my_param_Iter.next();
          Object[] newArray = new Object[my_currentParams.length + 1];
          for (int i = 1; i < my_param_Iter.next().length + 1; i++)
          {
            newArray[i] = my_currentParams[i];
          }
          newArray[0] = my_currentObj;
          
          return newArray;
        }
        else
        {
          return null;
        }
      }
      else
      {
        my_currentParams = my_param_Iter.next();
        Object[] newArray = new Object[my_currentParams.length+1];
        for (int i = 1; i < my_param_Iter.next().length+1; i++)
        {
          newArray[i] = my_currentParams[i];
        }
        newArray[0] = my_currentObj;
        
        return newArray;
      }
      
    }
    else
    {
      return null;
    }
  }
}

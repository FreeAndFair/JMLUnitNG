
package org.jmlspecs.jmlunitng;

import java.util.Iterator;

import org.multijava.mjc.JFormalParameter;

/**
 * This class combines the individual iterator for each data types and then
 * provides the combined iterator.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class CombinedParameterIterator implements Iterator
{
  /**
   * This array of iterator represents the Array of Iterators for all parameters
   * of a particular method.
   */
  protected final Iterator<Object>[] my_paramIterator;

  /**
   * This array of iterator represents the Array of Iterators for all parameters
   * of a particular method.
   */
  protected final Iterator<Object>[] my_pramArrayReassign;

  /**
   * This is the boolean field which is true if the iterator is accessing the
   * first element.
   */
  protected boolean isFirstElement;

  /**
   * Constructs the Combined Iterator object.
   * 
   * @param the_parameters
   * @param the_name
   */
  public CombinedParameterIterator(final Iterator[] the_paramIterator)
  {
    my_paramIterator = new Iterator[the_paramIterator.length];
    my_pramArrayReassign = new Iterator[the_paramIterator.length];
    for (int i = 0; i < the_paramIterator.length; i++)
    {
      my_paramIterator[i] = the_paramIterator[i];
      my_pramArrayReassign[i] = the_paramIterator[i];
      isFirstElement = true;
    }

  }

  /**
   * Returns true if the next element is present in the Combined Iterator.
   * 
   * @return boolean
   */
  public boolean hasNext()
  {
    boolean hasNextElement = true;
    for (int i = 0; i < my_paramIterator.length; i++)
    {
      if (!my_paramIterator[i].hasNext())
      {
        hasNextElement = false;
      }

    }
    return hasNextElement;
  }

  /**
   * Returns the combined array of parameters.
   * 
   * @return Object[]
   */
  public Object[] next()
  {
    Object[] combinedElements = new Object[my_paramIterator.length];

    if (isFirstElement)
    {
      for (int itCount = 0; itCount < my_paramIterator.length; itCount++)
      {
        combinedElements[itCount] = my_paramIterator[itCount].next();
      }
      isFirstElement = false;
    }
    else
    {
      for (int itCount = my_paramIterator.length - 1; itCount >= 0; itCount--)
      {
        if (my_paramIterator[itCount].hasNext())
        {
          combinedElements[itCount] = my_paramIterator[itCount];
          break;
        }
        else
        {
          if (itCount != 0)
          {
            combinedElements[itCount] = my_pramArrayReassign[itCount];
          }
        }
      }
    }
    return combinedElements;
  }

  /**
   * This method removes the element from the Iterator.
   */
  public void remove()
  {
    /*
     * Need to write the method here.
     */
  }
}

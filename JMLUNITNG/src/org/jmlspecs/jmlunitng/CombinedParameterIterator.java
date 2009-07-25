
package org.jmlspecs.jmlunitng;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.jmlspecs.jmlunit.strategies.IndefiniteIterator;
import org.jmlspecs.jmlunit.strategies.IntIterator;
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
  protected final ArrayList<Iterator> my_paramIterator;

  /**
   * This array of iterator represents the Array of Iterators for all parameters
   * of a particular method.
   */
  protected final ArrayList<Iterator> my_pramArrayReassign;

  /**
   * This is the boolean field which is true if the iterator is accessing the
   * first element.
   */
  protected boolean isFirstElement;

  /**
   *  This is the arraylist to store the elements.
   */
  protected List<ArrayList<Object>> storedArray;
  /**
   * This is the array of elements to be returned.
   */
  protected Object[] combinedElements;
  
  // Temp. counter.
  
  static protected int counter = 0;
  /**
   * Constructs the Combined Iterator object.
   * 
   * @param the_parameters
   * @param the_name
   */
  public CombinedParameterIterator(final ArrayList<IndefiniteIterator> the_paramIterator)
  {
    
    my_paramIterator = new ArrayList<Iterator>();
    my_pramArrayReassign = new ArrayList<Iterator>();
    storedArray = new ArrayList<ArrayList<Object>>();
    for(int i = 0; i < the_paramIterator.size(); i++)
    {
      ArrayList<Object> tempList = new ArrayList<Object>();
      while(!the_paramIterator.get(i).atEnd())
      {
        tempList.add(the_paramIterator.get(i).get());
        the_paramIterator.get(i).advance();
      }
      storedArray.add(tempList);
      my_paramIterator.add(tempList.iterator());
      my_pramArrayReassign.add(tempList.iterator());
    }
    isFirstElement = true;
    combinedElements = new Object[my_paramIterator.size()];
   
  }

  /**
   * Returns true if the next element is present in the Combined Iterator.
   * 
   * @return boolean
   */
  public boolean hasNext()
  {
    boolean hasNextElement = false;
 
   
    for (int i = 0; i < my_paramIterator.size(); i++)
    {
      if(my_paramIterator.get(i).hasNext())
      {
        hasNextElement = true;
        break;
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
    

    if (isFirstElement)
    {
      for (int itCount = 0; itCount < my_paramIterator.size(); itCount++)
      {
        combinedElements[itCount] = my_paramIterator.get(itCount).next();
        
      }
      isFirstElement = false;
    }
    else
    {
      
      for (int itCount = my_paramIterator.size() - 1; itCount >= 0; itCount--)
      {
      
        if (!my_paramIterator.get(itCount).hasNext())
        {
          if (itCount != 0)
          {
            
           // combinedElements[itCount] = my_paramIterator.get(itCount).get();
            my_paramIterator.remove(itCount);
           
            my_paramIterator.add(itCount, storedArray.get(itCount).iterator());
            
            combinedElements[itCount] = my_paramIterator.get(itCount).next();
            
            
          }
          else
          {
            //combinedElements[itCount] = my_paramIterator.get(itCount).get();
            
          }
          
        }
        else
        {
          combinedElements[itCount] = my_paramIterator.get(itCount).next();
          break;
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

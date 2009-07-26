
package org.jmlspecs.jmlunitng;

import java.util.ArrayList;
import java.util.Iterator;

import org.jmlspecs.jmlunit.strategies.IndefiniteIterator;

import com.sun.corba.se.spi.ior.ObjectId;

/**
 * This class provides functionality to combine the CombinedParameterIterator
 * with object Iterator.
 * 
 * @author Rinkesh Nagmoti.
 * @version 1.0
 */
public class CombinedObjectParameterIterator implements Iterator
{

  /**
   * This is the combined parameter iterator.
   */

  protected Iterator<Object[]> paramIter;
  /**
   * This is the object iterator.
   */
  private Iterator<Object> objIter;
  /**
   * This is the current object.
   */
  private Object currentObj;
  /**
   * This is the current parameters array.
   */
  private Object[] currentParams;

  /**
   * This is the Iterator for reassignment.
   */
  private ArrayList<Object[]> paramReassign;

  
  /**
   * Constructs the object of CombinedObjectParameterIterator.
   */
  public CombinedObjectParameterIterator(final CombinedParameterIterator the_paraIter,
                                         final Iterator<Object> the_objIter)
  {
    
   
    paramReassign = new ArrayList<Object[]>();
    int cnt =0;
    while(the_paraIter.hasNext())
    {
      Object[] tempArray = the_paraIter.next();
      Object[] newArray = new Object[tempArray.length];
      for(int i = 0; i < tempArray.length; i++)
      {
        newArray[i] = tempArray[i];
        
      }
      
      paramReassign.add(newArray);
     
      cnt++;
    }
 
       
    
    
    paramIter = paramReassign.iterator();
   
    objIter = the_objIter;
   // paramReassign = the_paraIter;
  }

  /**
   * This method returns true if any of the iterators has the next element.
   * 
   * @return boolean.
   */
  public boolean hasNext()
  {
    if (paramIter.hasNext() || objIter.hasNext())
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
   * 
   * @return Object[]
   */
  public Object[] next()
  {
    if (paramIter.hasNext() || objIter.hasNext())
    {
      if (currentObj == null)
      {
        currentObj = objIter.next();
       
        currentParams = paramIter.next();
        Object[] newArray = new Object[currentParams.length + 1];
        for (int i = 1; i < currentParams.length + 1; i++)
        {
          newArray[i] = currentParams[i - 1];
        }
        newArray[0] = currentObj;
       
        return newArray;
      }
      else
      {
        if (paramIter.hasNext())
        {
          currentParams = paramIter.next();
         
          Object[] newArray = new Object[currentParams.length + 1];
          for (int i = 1; i < currentParams.length + 1; i++)
          {
            newArray[i] = currentParams[i-1];
          }
          newArray[0] = currentObj;
         
          return newArray;
        }
        else
        {
          if (objIter.hasNext())
          {
            currentObj = objIter.next();
            
            paramIter = paramReassign.iterator();
           
            currentParams = paramIter.next();
            Object[] newArray = new Object[currentParams.length + 1];
            for (int i = 1; i < currentParams.length + 1; i++)
            {
              newArray[i] = currentParams[i-1];
            }
            newArray[0] = currentObj;
           
            return newArray;
          }
          else
          {
          
            return null;
          }
        }
      }
    }
    
    else
    {
    
      return null;
    }
   

  }

  /**
   * This method removes the next element from the iterator.
   */
  public void remove()
  {
    if (objIter.hasNext())
    {
      if (paramIter.hasNext())
      {
        paramIter.remove();
      }
      
    }
    else
    {
      if (paramIter.hasNext())
      {
        paramIter.remove();
      }
    }
  }
}

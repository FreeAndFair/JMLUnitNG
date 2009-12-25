package org.jmlspecs.jmlunitng.strategies;

import java.util.Iterator;

/**
 * Adapts a "real" Java iterator to our internal StrategyIterator interface.
 * 
 * @author Daniel M. Zimmerman
 * @version JMLUnitNG Very Pre-Beta
 */
public class IteratorAdapter implements StrategyIterator
{
  private int count = 0;
  
  /**
   * The "current" element.
   */
  private Object my_current;
  
  /**
   * A boolean indicating whether we are at the end or not.
   */
  private boolean my_at_end;
  
  /**
   * The iterator.
   */
  private Iterator<Object> my_iterator;
  
  /**
   * Constructs a new IteratorAdapter with the specified iterator.
   * 
   * @param the_iterator The iterator.
   */
  public IteratorAdapter(final Iterator<Object> the_iterator)
  {
    my_iterator = the_iterator;
    if (my_iterator.hasNext())
    {
      my_current = my_iterator.next();
      my_at_end = false;
    }
  }
  
  /**
   * Advances the iterator to the next element.
   */
  public void advance()
  {
    count++;
    if (my_iterator.hasNext())
    {
      my_current = my_iterator.next();
    }
    else if (my_at_end)
    {
      throw new IllegalArgumentException("invalid call");
    }
    else
    {
      my_at_end = true;
    }
  }

  public boolean atEnd()
  {
    return my_at_end;
  }

  public Object get()
  {
    return my_current;
  }

}

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
  /**
   * The "current" element.
   */
  private Object my_current;
  
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
  }
  
  /**
   * Advances the iterator to the next element.
   */
  public void advance()
  {
    if (my_iterator.hasNext())
    {
      my_current = my_iterator.next();
    }
  }

  public boolean atEnd()
  {
    return !my_iterator.hasNext();
  }

  public Object get()
  {
    return my_current;
  }

}

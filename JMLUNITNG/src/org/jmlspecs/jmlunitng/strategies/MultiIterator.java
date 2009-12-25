
package org.jmlspecs.jmlunitng.strategies;

/**
 * This class combines multiple iterators into one iterator.
 * 
 * @author Daniel M. Zimmerman
 * @version 1.0
 */
public class MultiIterator implements StrategyIterator
{
  /**
   * The current iterator being used.
   */
  private transient int my_current_iterator;
  
  /**
   * The iterators to use.
   */
  private transient StrategyIterator[] my_iterators;
  
  /**
   * Constructs a new MultiIterator with the specified iterators.
   * 
   * @param the_iterators The iterators.
   */
  public MultiIterator(final StrategyIterator... the_iterators)
  {
    my_iterators = the_iterators.clone();
    my_current_iterator = 0;
    while (my_current_iterator < my_iterators.length && 
           my_iterators[my_current_iterator].atEnd())
    {
      my_current_iterator = my_current_iterator + 1;
    }
  }

  /* (non-Javadoc)
   * @see org.jmlspecs.jmlunitng.strategies.StrategyIterator#get()
   */
  public final Object get()
  {
    if (!atEnd())
    {
      return my_iterators[my_current_iterator].get();
    }
    else
    {
      throw new IllegalStateException("invalid call");
    }
  }

  /* (non-Javadoc)
   * @see org.jmlspecs.jmlunitng.strategies.StrategyIterator#atEnd()
   */
  public final boolean atEnd()
  {
    // "at the end" means we're past the last iterator or 
    // have no iterators left with items
    
    boolean no_more_items = true;
    for (int i = my_current_iterator; i < my_iterators.length; i++)
    {
      no_more_items = no_more_items && my_iterators[i].atEnd();
    }
    
    return no_more_items;
  }

  /* (non-Javadoc)
   * @see org.jmlspecs.jmlunitng.strategies.StrategyIterator#advance()
   */
  public final void advance()
  {
    if (atEnd())
    {
      throw new IllegalStateException("invalid call");
    }
    
    if (!my_iterators[my_current_iterator].atEnd())
    {
      my_iterators[my_current_iterator].advance();
    }
    
    while (my_current_iterator < my_iterators.length && 
           my_iterators[my_current_iterator].atEnd())
    {
      my_current_iterator = my_current_iterator + 1;
    }
  }
}

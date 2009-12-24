
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
  public Object get()
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
  public boolean atEnd()
  {
    // "at the end" means we're on the last iterator, and it's at the end,
    // or we're past the last iterator
    
    boolean result = my_iterators.length <= my_current_iterator;
    result = result || 
             (my_current_iterator == my_iterators.length - 1 &&
              my_iterators[my_current_iterator].atEnd());
    return result;
  }

  /* (non-Javadoc)
   * @see org.jmlspecs.jmlunitng.strategies.StrategyIterator#advance()
   */
  public void advance()
  {
    if (atEnd())
    {
      throw new IllegalStateException("invalid call");
    }
    else if (my_iterators[my_current_iterator].atEnd())
    {
      while (my_current_iterator < my_iterators.length && 
             my_iterators[my_current_iterator].atEnd())
      {
        my_current_iterator = my_current_iterator + 1;
      }
    }
    else
    {
      my_iterators[my_current_iterator].advance();
    }
  }
}

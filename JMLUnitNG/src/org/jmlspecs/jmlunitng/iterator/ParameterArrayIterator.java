/*
 * JMLUnitNG Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

import org.jmlspecs.jmlunitng.strategy.Strategy;

/**
 * A repeated access iterator that generates arrays of objects by reflectively
 * instantiating iterator classes that contain test parameter data.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version July 2011
 */
public class ParameterArrayIterator implements RepeatedAccessIterator<Object[]> {
  /**
   * The list of iterator generation methods.
   */
  private final Class<? extends Strategy>[] my_strategy_classes;

  /**
   * The current strategies being used.
   */
  // @ private invariant my_strategies.length == my_strategy_classes.length;
  private RepeatedAccessIterator<?>[] my_strategies;

  /**
   * A flag indicating whether there are elements remaining.
   */
  private boolean my_is_finished;

  /**
   * Creates a new ObjectArrayIterator that iterates over all combinations of
   * objects in the given Strategy classes.
   * 
   * @param the_strategy_classes The strategies to iterate over.
   * @throws IllegalArgumentException if there is a problem calling the
   *           constructors of the strategy classes.
   */
  /*
   * @ requires (\forall int i; i >= 0 && i < the_strategy_classes.length;
   * 
   * @ the_strategy_classes[i].newInstance().iterator().hasElement());
   * 
   * @
   */
  public ParameterArrayIterator(final Class<? extends Strategy>... the_strategy_classes) {
    my_strategy_classes = the_strategy_classes;
    my_strategies = new RepeatedAccessIterator<?>[the_strategy_classes.length];
    my_is_finished = the_strategy_classes.length == 0;
    for (int i = 0; i < my_strategies.length; i++) {
      try {
        my_strategies[i] = the_strategy_classes[i].newInstance().iterator();
      } catch (final InstantiationException e) {
        throw new IllegalArgumentException(e);
      } catch (final IllegalAccessException e) {
        throw new IllegalArgumentException(e);
      }
    }
  }
  
  /**
   * {@inheritDoc}
   */
  public Object[] element() {
    final Object[] result = new Object[my_strategies.length];
    for (int i = 0; i < my_strategies.length; i++) {
      if (my_strategies[i].hasElement()) {
        result[i] = my_strategies[i].element();
      } else {
        result[i] = null;
      }
    }
    return result;
  }

  /**
   * {@inheritDoc}
   */
  public boolean hasElement() {
    return !my_is_finished;
  }

  /**
   * {@inheritDoc}
   */
  // @ requires hasElement();
  public void advance() {
    try {
      int p = 0;
      while (p < my_strategies.length) {
        // ensure each iterator is at a valid element
        my_strategies[p].advance();
        if (my_strategies[p].hasElement()) {
          // no need to check the other iterators
          break;
        } else {
          my_strategies[p] =
              (RepeatedAccessIterator<?>) my_strategy_classes[p].newInstance().iterator();
          p++;
        }
      }
      // if we've reset the last iterator, we're done
      my_is_finished = p == my_strategies.length;
    } catch (final InstantiationException e) {
      // this should never happen because we checked them earlier
      System.err.println(e);
    } catch (final IllegalAccessException e) {
      // neither should this
      System.err.println(e);
    }
  }
}

/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.iterator;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import org.jmlspecs.jmlunitng.strategy.Strategy;

/**
 * A repeated access iterator that generates arrays of objects of a specific
 * type and maximum length by reflectively instantiating iterator classes to
 * supply data for the array components.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public class DynamicArrayIterator implements RepeatedAccessIterator<Object> {
  /**
   * The component type of the generated array.
   */
  private final Class<?> my_component_type;

  /**
   * The list of iterator generation methods.
   */
  private final List<Class<? extends Strategy>> my_strategy_classes;

  /**
   * The maximum length of arrays to generate.
   */
  private final int my_max_length;

  /**
   * The current strategies being used.
   */
  private RepeatedAccessIterator<?>[] my_strategies;

  /**
   * The most recently generated array (current element).
   */
  private Object my_element;

  /**
   * A flag indicating whether there are elements remaining.
   */
  private boolean my_is_finished;

  /**
   * Creates a new DynamicArrayIterator that generates arrays of the specified
   * component type using the specified strategy classes to provide data, up to
   * the specified maximum array length.
   * 
   * @param the_component_type The component type of the generated arrays.
   * @param the_strategy_classes The strategy classes to use to populate the
   *          arrays.
   * @param the_max_length The maximum array length.
   * @throws IllegalArgumentException if there is a problem calling the
   *           constructors of the strategy classes.
   */
  public DynamicArrayIterator(final Class<?> the_component_type,
                              final List<Class<? extends Strategy>> the_strategy_classes,
                              final int the_max_length) throws IllegalArgumentException {
    my_component_type = the_component_type;
    my_strategy_classes = 
      new ArrayList<Class<? extends Strategy>>(the_strategy_classes);
    my_max_length = the_max_length;
    my_strategies = new RepeatedAccessIterator<?>[0];
    my_element = Array.newInstance(the_component_type, 0);
    my_is_finished = my_strategy_classes.isEmpty();

    // check the strategy classes to see that they all work
    for (Class<? extends Strategy> c : my_strategy_classes) {
      try {
        c.newInstance();
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
  public Object element() throws NoSuchElementException {
    if (my_is_finished) {
      throw new NoSuchElementException("iterator has no current element");
    }
    return my_element;
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
  public void advance() {
    int p = 0;
    while (p < my_strategies.length) {
      // ensure each iterator is at a valid element
      my_strategies[p].advance();
      if (my_strategies[p].hasElement()) {
        // no need to check the other iterators
        break;
      } else {
        // leave the strategy empty for later refilling
        p++;
      }
    }

    my_is_finished = p == my_strategies.length && my_strategies.length == my_max_length;

    if (strategiesAreEmpty() && !my_is_finished) {
      // bump up the array length
      my_strategies = new RepeatedAccessIterator<?>[my_strategies.length + 1];
      for (int i = 0; i < my_strategies.length; i++) {
        my_strategies[i] = newStrategy();
      }
    }
    
    if (!my_is_finished) {
      // refill all the strategies that need it
      for (int i = 0; i < my_strategies.length; i++) {
        if (!my_strategies[i].hasElement()) {
          my_strategies[i] = newStrategy();
        }
      }

      my_element = Array.newInstance(my_component_type, my_strategies.length);
      for (int i = 0; i < my_strategies.length; i++) {
        Array.set(my_element, i, my_strategies[i].element());
      } 
    } // else the element stays at its default value
  }

  /**
   * @return true if there are no values left in our strategies, false
   *         otherwise; note that this always returns false for the strategy
   *         array of size 0.
   */
  private boolean strategiesAreEmpty() {
    boolean result = false;
    for (RepeatedAccessIterator<?> s : my_strategies) {
      result = result || s.hasElement();
    }
    return !result;
  }

  /**
   * @return a new strategy for an array element, comprised of the concatenation
   *         of all the strategy classes specified at construction.
   */
  @SuppressWarnings({ "unchecked", "rawtypes" })
  private RepeatedAccessIterator<?> newStrategy() {
    final List<RepeatedAccessIterator<?>> strategy_list =
        new LinkedList<RepeatedAccessIterator<?>>();
    for (Class<? extends Strategy> c : my_strategy_classes) {
      try {
        strategy_list.add(c.newInstance().iterator());
      } catch (final InstantiationException e) {
        // this should never happen because we checked them earlier
        System.err.println(e);
      } catch (final IllegalAccessException e) {
        // this should never happen because we checked them earlier
        System.err.println(e);
      }
    }
    return new MultiIterator(strategy_list);
  }
}

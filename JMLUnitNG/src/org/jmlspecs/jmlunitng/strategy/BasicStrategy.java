/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.strategy;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.MultiIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * The basic framework of a test data generation strategy.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public abstract class BasicStrategy {
  /**
   * To be implemented by subclasses. Returns the iterator over default values
   * for this type.
   * 
   * @return What are your default values?
   */
  public abstract RepeatedAccessIterator<?> getDefaultValues();

  // "What is your custom set of values?",
  /**
   * To be implemented by users. Returns an iterator over the custom values
   * for this type.
   * 
   * @return What are your custom values?
   */
  public abstract RepeatedAccessIterator<?> getCustomValues();

  /**
   * To be implemented by users. Returns an iterator over the global values for
   * this type.
   * 
   * @return What are your global values?
   */
  public abstract RepeatedAccessIterator<?> getGlobalValues();

  /**
   * Returns a RepeatedAccessIterator over all values in the order: default
   * values, custom values, global values.
   * 
   * @return What are all your values?
   */
  @SuppressWarnings("unchecked")
  public RepeatedAccessIterator<?> iterator() {
    final List<RepeatedAccessIterator<?>> iterators = new ArrayList<RepeatedAccessIterator<?>>(3);
    iterators.add(getDefaultValues());
    iterators.add(getCustomValues());
    iterators.add(getGlobalValues());
    return new MultiIterator(iterators);
  }
}

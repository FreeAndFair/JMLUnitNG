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

package org.jmlspecs.openjmlunit.strategy;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjmlunit.iterator.MultiIterator;
import org.jmlspecs.openjmlunit.iterator.RepeatedAccessIterator;

/**
 * The basic framework of a test data generation strategy.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class BasicStrategy {

  // query
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * 
   * @return An Iterator over default values.
   */
  public abstract RepeatedAccessIterator<?> getDefaultValues();

  // "What is your custom set of values?",
  /**
   * To be implemented by users. Returns an iterator over the custom values.
   * 
   * @return An Iterator over custom values.
   */
  public abstract RepeatedAccessIterator<?> getCustomValues();

  // "What is your global set of values?",
  /**
   * To be implemented by users. Returns an iterator over the global values for
   * this type.
   * 
   * @return An Iterator over global values.
   */
  public abstract RepeatedAccessIterator<?> getGlobalValues();

  // "What is an iterator over all your sets of values?"
  /**
   * Returns a RepeatedAccessIterator over all values in the order: default
   * values, custom values, global values.
   * 
   * @return Iterator over all values.
   */
  public RepeatedAccessIterator<?> iterator() {
    final List<RepeatedAccessIterator<?>> iterators = new ArrayList<RepeatedAccessIterator<?>>(3);
    iterators.add(getDefaultValues());
    iterators.add(getCustomValues());
    iterators.add(getGlobalValues());
    return new MultiIterator(iterators);
  }
}

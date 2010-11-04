/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.strategy;

import java.util.SortedSet;
import java.util.TreeSet;

import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * The basic framework of a primitive test data generation strategy. 
 * Primitive data strategies deduplicate the test data elements to save
 * on test executions, since they are all in memory anyway.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version November 2010
 */
public abstract class PrimitiveStrategy implements Strategy {
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
  public RepeatedAccessIterator<Comparable<?>> iterator() {
    // deduplicate the primitive data, because we can easily keep it all in memory
    // at once and this saves test executions; note that all primitive types,
    // including String, are Comparable, so we sort them too so that tests end
    // up being executed in a reasonable order.
    
    final SortedSet<Comparable<?>> set = new TreeSet<Comparable<?>>();
    RepeatedAccessIterator<?>[] values = { getDefaultValues(), getCustomValues(), getGlobalValues() };
    for (RepeatedAccessIterator<?> r : values) {
      while (r.hasElement()) {
        set.add((Comparable<?>) r.element());
        r.advance();
      }
    }
    return new IteratorAdapter<Comparable<?>>(set.iterator());
  }
}

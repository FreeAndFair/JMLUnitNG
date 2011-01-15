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
 * on redundant test executions.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version November 2010
 */
public abstract class PrimitiveStrategy implements Strategy {
  /**
   * To be implemented by users. Returns an iterator over the local-scope
   * values for this type.
   * 
   * @return What are your local-scope values?
   */
  public abstract RepeatedAccessIterator<?> getLocalValues();

  /**
   * To be implemented by automatically-generated strategy classes. 
   * Returns an iterator over the class-scope values for this type.
   * 
   * @return What are your class-scope values?
   */
  public abstract RepeatedAccessIterator<?> getClassValues();

  /**
   * To be implemented by automatically-generated strategy classes. 
   * Returns an iterator over the package-scope values for this type.
   * 
   * @return What are your package-scope values?
   */
  public abstract RepeatedAccessIterator<?> getPackageValues();
  
  /**
   * To be implemented by subclasses. Returns the iterator over default 
   * values for this type.
   * 
   * @return What are your default values?
   */
  public abstract RepeatedAccessIterator<?> getDefaultValues();

  /**
   * Returns a RepeatedAccessIterator over all values.
   * 
   * @return What are all your values?
   */
  public RepeatedAccessIterator<Comparable<?>> iterator() {
    // deduplicate the primitive data, because we can easily keep it all in memory
    // at once and this saves test executions; note that all primitive types,
    // including String, are Comparable, so we sort them too so that tests end
    // up being executed in a reasonable order.
    
    final SortedSet<Comparable<?>> set = new TreeSet<Comparable<?>>();
    final RepeatedAccessIterator<?>[] values = 
      { getLocalValues(), getClassValues(), getPackageValues(), getDefaultValues() };
    for (RepeatedAccessIterator<?> r : values) {
      while (r.hasElement()) {
        set.add((Comparable<?>) r.element());
        r.advance();
      }
    }
    return new IteratorAdapter<Comparable<?>>(set.iterator());
  }
}

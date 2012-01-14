/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import org.jmlspecs.jmlunitng.iterator.IteratorSampler;
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * The basic framework of a primitive test data generation strategy. 
 * Primitive data strategies deduplicate the test data values to save
 * on redundant test executions.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public abstract class PrimitiveStrategy extends AbstractStrategy {
  /**
   * To be implemented by subclasses. Returns the iterator over default 
   * values for this type.
   * 
   * @return What are your default values?
   */
  public abstract RepeatedAccessIterator<?> defaultValues();
  
  /**
   * Returns a RepeatedAccessIterator over a fraction of the strategy
   * values, as specified by configuration methods.
   * 
   * @return What are your values?
   */
  public RepeatedAccessIterator<Comparable<?>> iterator() {
    // deduplicate the primitive data, because we can easily keep it all in memory
    // at once and this saves test executions; note that all primitive types,
    // including String, are Comparable, so we sort them too so that tests end
    // up being executed in a reasonable order - being careful to correctly handle
    // the null string so it doesn't get compared and cause an exception.
    
    boolean add_null = false;
    final SortedSet<Comparable<?>> data_set = new TreeSet<Comparable<?>>();
    final RepeatedAccessIterator<?>[] values = 
    { localValues(), classValues(), packageValues(), defaultValues() };
    for (RepeatedAccessIterator<?> r : values) {
      while (r.hasElement()) {
        final Comparable<?> element = (Comparable<?>) r.element();
        if (element == null) {
          add_null = true; 
        } else {
          data_set.add(element);
        }
        r.advance();
      }
    }
    final List<Comparable<?>> data_list = new ArrayList<Comparable<?>>();
    if (add_null) {
      data_list.add(null);
    }
    data_list.addAll(data_set);
    RepeatedAccessIterator<Comparable<?>> result = 
      new ObjectArrayIterator<Comparable<?>>
      (data_list.toArray(new Comparable[data_list.size()]));
    // TODO Make this more efficient!
    if (fraction() < 1.0) {
      result = new IteratorSampler<Comparable<?>>(result, fraction(), seed());
    }
    return result;
  }
}

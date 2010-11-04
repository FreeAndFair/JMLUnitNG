/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * All values in all sets of values are assignable to Java type 'long'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class LongStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Long> DEFAULT_VALUES;
  static {
    final List<Long> defs = new ArrayList<Long>(3);
    defs.add(-1L);
    defs.add(0L);
    defs.add(1L);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Long>(DEFAULT_VALUES.iterator());
  }
}

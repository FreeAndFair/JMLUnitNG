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
 * The default strategy for the <code>double</code> type. The default values are 
 * -1.0, 0.0 and 1.0.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version December 2010
 */
public abstract class DoubleStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Double> DEFAULT_VALUES;
  static {
    final List<Double> defs = new ArrayList<Double>(3);
    defs.add(-1.0);
    defs.add(0.0);
    defs.add(1.0);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Double>(DEFAULT_VALUES.iterator());
  }
}

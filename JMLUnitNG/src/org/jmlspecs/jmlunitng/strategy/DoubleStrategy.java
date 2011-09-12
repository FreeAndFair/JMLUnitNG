/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for the <code>double</code> type. The default values are 
 * -1.0, 0.0 and 1.0.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class DoubleStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Double> DEFAULT_VALUES;
  static {
    final List<Double> defs = new ArrayList<Double>(3);
    defs.add(Double.NEGATIVE_INFINITY);
    defs.add(0.0);
    defs.add(Double.POSITIVE_INFINITY);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Double>(new Double[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Double>(new Double[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Double>(new Double[0]);
  }
  
  /**
   * @return an iterator over the default double values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new IteratorAdapter<Double>(DEFAULT_VALUES.iterator());
  }
}

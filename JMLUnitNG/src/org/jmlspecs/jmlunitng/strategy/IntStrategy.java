/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for the <code>int</code> type. The default values are 
 * -1, 0 and 1.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class IntStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final Integer[] DEFAULT_VALUES = 
  { Integer.MIN_VALUE, 0, Integer.MAX_VALUE };
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Integer>(new Integer[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Integer>(new Integer[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Integer>(new Integer[0]);
  }
  
  /**
   * @return an iterator over the default int values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<Integer>(DEFAULT_VALUES);
  }
}

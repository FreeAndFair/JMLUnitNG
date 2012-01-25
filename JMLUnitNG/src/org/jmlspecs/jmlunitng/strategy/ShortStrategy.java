/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * The default strategy for the <code>short</code> type. The default values are 
 * -1, 0 and 1.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class ShortStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final Short[] DEFAULT_VALUES = 
  { Short.MIN_VALUE, 0, Short.MAX_VALUE };
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Short>(new Short[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Short>(new Short[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Short>(new Short[0]);
  }
  
  /**
   * @return an iterator over the default short values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<Short>(DEFAULT_VALUES);
  }
}

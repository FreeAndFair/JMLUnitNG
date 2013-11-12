/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for the <code>boolean</code> type. The default 
 * (and only possible) values are <code>true</code> and <code>false</code>.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class BooleanStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final Boolean[] DEFAULT_VALUES = { Boolean.TRUE, Boolean.FALSE };
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Boolean>(new Boolean[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Boolean>(new Boolean[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Boolean>(new Boolean[0]);
  }
  
  /**
   * @return an iterator over the default boolean values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<Boolean>(DEFAULT_VALUES);
  }
}

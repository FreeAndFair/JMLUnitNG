/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for the <code>byte</code> type. The default values are 
 * -1, 0 and 1.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class ByteStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final Byte[] DEFAULT_VALUES = { Byte.MIN_VALUE, 0, Byte.MAX_VALUE };
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Byte>(new Byte[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Byte>(new Byte[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Byte>(new Byte[0]);
  }
  
  /**
   * @return an iterator over the default byte values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<Byte>(DEFAULT_VALUES);  
  }
}

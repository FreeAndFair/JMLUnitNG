/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for the <code>char</code> type. The default values are 
 * 0 and 1.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class CharStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final Character[] DEFAULT_VALUES = 
  { Character.MIN_VALUE, Character.MAX_VALUE };
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Character>(new Character[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Character>(new Character[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Character>(new Character[0]);
  }
  
  /**
   * @return an iterator over the default char values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<Character>(DEFAULT_VALUES);  
  }
}

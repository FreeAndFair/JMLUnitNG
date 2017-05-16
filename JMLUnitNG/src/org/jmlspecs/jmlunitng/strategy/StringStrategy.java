/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for type <code>java.lang.String</code>, which - although an
 * object - is treated as primitive by JMLUnitNG. The default values are <code>null</code>
 * and <code>""</code> (the empty string).
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class StringStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final String[] DEFAULT_VALUES = { null, "" };
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<String>(new String[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<String>(new String[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<String>(new String[0]);
  }
  
  /**
   * @return an iterator over the default String values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<String>(DEFAULT_VALUES);
  }
}

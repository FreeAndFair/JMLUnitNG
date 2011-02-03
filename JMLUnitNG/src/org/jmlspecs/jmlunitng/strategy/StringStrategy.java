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
  private static final List<String> DEFAULT_VALUES;
  static {
    final List<String> defs = new ArrayList<String>(2);
    defs.add(null);
    defs.add("");
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
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
    return new IteratorAdapter<String>(DEFAULT_VALUES.iterator());
  }
}

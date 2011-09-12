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
  private static final List<Integer> DEFAULT_VALUES;
  static {
    final List<Integer> defs = new ArrayList<Integer>(3);
    defs.add(Integer.MIN_VALUE);
    defs.add(0);
    defs.add(Integer.MAX_VALUE);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
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
    return new IteratorAdapter<Integer>(DEFAULT_VALUES.iterator());
  }
}

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
  private static final List<Boolean> DEFAULT_VALUES;
  static {
    final List<Boolean> defs = new ArrayList<Boolean>(2);
    defs.add(true);
    defs.add(false);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
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
    return new IteratorAdapter<Boolean>(DEFAULT_VALUES.iterator());
  }
}

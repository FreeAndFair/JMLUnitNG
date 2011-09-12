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
  private static final List<Short> DEFAULT_VALUES;
  static {
    final List<Short> defs = new ArrayList<Short>(3);
    defs.add(Short.MIN_VALUE);
    defs.add((short) 0);
    defs.add(Short.MAX_VALUE);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
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
    return new IteratorAdapter<Short>(DEFAULT_VALUES.iterator());
  }
}

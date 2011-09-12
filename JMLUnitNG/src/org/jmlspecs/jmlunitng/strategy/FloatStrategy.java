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
 * The default strategy for the <code>float</code> type. The default values are 
 * -1.0, 0.0 and 1.0.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class FloatStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Float> DEFAULT_VALUES;
  static {
    final List<Float> defs = new ArrayList<Float>(3);
    defs.add(Float.NEGATIVE_INFINITY);
    defs.add(0.f);
    defs.add(Float.POSITIVE_INFINITY);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Float>(new Float[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Float>(new Float[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Float>(new Float[0]);
  }
  
  /**
   * @return an iterator over the default float values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new IteratorAdapter<Float>(DEFAULT_VALUES.iterator());
  }
}

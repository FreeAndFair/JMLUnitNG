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
  private static final List<Character> DEFAULT_VALUES;
  static {
    final List<Character> defs = new ArrayList<Character>(2);
    defs.add(Character.MIN_VALUE);
    defs.add(Character.MAX_VALUE);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  
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
    return new IteratorAdapter<Character>(DEFAULT_VALUES.iterator());
  }
}

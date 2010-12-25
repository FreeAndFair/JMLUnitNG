/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * The default strategy for the <code>char</code> type. The default values are 
 * 0 and 1.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version December 2010
 */
public abstract class CharStrategy extends PrimitiveStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Character> DEFAULT_VALUES;
  static {
    final List<Character> defs = new ArrayList<Character>(2);
    defs.add((char) 0);
    defs.add((char) 1);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Character>(DEFAULT_VALUES.iterator());
  }
}

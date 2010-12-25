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
 * The default strategy for the <code>boolean</code> type. The default 
 * (and only possible) values are <code>true</code> and <code>false</code>.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version December 2010
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
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Boolean>(DEFAULT_VALUES.iterator());
  }
}

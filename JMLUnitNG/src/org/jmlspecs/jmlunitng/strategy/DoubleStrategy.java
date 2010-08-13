/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "April 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */
package org.jmlspecs.jmlunitng.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
/**
 * All values in all sets of values are assignable to Java type 'double'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class DoubleStrategy extends BasicStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Double> DEFAULT_VALUES;
  static {
    final List<Double> defs = new ArrayList<Double>(3);
    defs.add(-1.0);
    defs.add(0.0);
    defs.add(1.0);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Double>(DEFAULT_VALUES.iterator());
  }
}
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
 * All values in all sets of values are assignable to Java type 'shor'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class ShortStrategy extends BasicStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Short> DEFAULT_VALUES;
  static {
    final List<Short> defs = new ArrayList<Short>(3);
    defs.add((short) -1);
    defs.add((short) 0);
    defs.add((short) 1);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Short>(DEFAULT_VALUES.iterator());
  }
}
/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "April 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */
package org.jmlspecs.openjmlunit.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jmlspecs.openjmlunit.iterator.IteratorAdapter;
import org.jmlspecs.openjmlunit.iterator.RepeatedAccessIterator;
/**
 * All values in all sets of values are assignable to Java type 'char'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class CharStrategy extends BasicStrategy {
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

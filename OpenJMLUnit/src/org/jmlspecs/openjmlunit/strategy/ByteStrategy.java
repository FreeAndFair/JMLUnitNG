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
 * All values in all sets of values are assignable to Java type 'byte'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class ByteStrategy extends BasicStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Byte> DEFAULT_VALUES;
  static {
    final List<Byte> defs = new ArrayList<Byte>(3);
    defs.add((byte) -1);
    defs.add((byte) 0);
    defs.add((byte) 1);
    DEFAULT_VALUES = Collections.unmodifiableList(defs);
  }
  /**
   * To be implemented by subclasses. Returns the iterator over default values.
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    return new IteratorAdapter<Byte>(DEFAULT_VALUES.iterator());
  }
}

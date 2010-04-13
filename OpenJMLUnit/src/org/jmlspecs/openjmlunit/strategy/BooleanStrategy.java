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
import java.util.Iterator;
import java.util.List;
/**
 * All values in all sets of values are assignable to Java type 'boolean'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class BooleanStrategy extends BasicStrategy {
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
  public Iterator<?> getDefaultValues() {
    return DEFAULT_VALUES.iterator();
  }
}

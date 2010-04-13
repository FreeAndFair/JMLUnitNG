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
 * All values in all sets of values are assignable to Java type 'float'.
 * @author Jonathan Hogins
 * @version April 2010
 */
public abstract class FloatStrategy extends BasicStrategy {
  /**
   * The default values for this strategy.
   */
  private static final List<Float> DEFAULT_VALUES;
  static {
    final List<Float> defs = new ArrayList<Float>(3);
    defs.add(-1.f);
    defs.add(0.f);
    defs.add(1.f);
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

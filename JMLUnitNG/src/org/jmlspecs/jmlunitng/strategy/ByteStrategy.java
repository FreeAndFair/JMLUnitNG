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
 * The default strategy for the <code>byte</code> type. The default values are 
 * -1, 0 and 1.
 *
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version January 2011
 */
public abstract class ByteStrategy extends PrimitiveStrategy {
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
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Byte>(new Byte[0]);
  }
  
  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Byte>(new Byte[0]);
  }

  /**
   * A default empty iterator, to be overridden by child classes.
   * 
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Byte>(new Byte[0]);
  }
  
  /**
   * @return an iterator over the default byte values.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new IteratorAdapter<Byte>(DEFAULT_VALUES.iterator());
  }
}

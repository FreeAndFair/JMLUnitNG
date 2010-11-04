/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * A test data generation strategy.
 * 
 * @author Daniel M. Zimmerman
 * @version November 2010
 */
public interface Strategy {
  /**
   * To be implemented by subclasses. Returns the iterator over default values
   * for this type.
   * 
   * @return What are your default values?
   */
  RepeatedAccessIterator<?> getDefaultValues();

  // "What is your custom set of values?",
  /**
   * To be implemented by users. Returns an iterator over the custom values
   * for this type.
   * 
   * @return What are your custom values?
   */
  RepeatedAccessIterator<?> getCustomValues();

  /**
   * To be implemented by users. Returns an iterator over the global values for
   * this type.
   * 
   * @return What are your global values?
   */
  RepeatedAccessIterator<?> getGlobalValues();

  /**
   * Returns a RepeatedAccessIterator over all values in the order: default
   * values, custom values, global values.
   * 
   * @return What are all your values?
   */
  RepeatedAccessIterator<?> iterator();
}

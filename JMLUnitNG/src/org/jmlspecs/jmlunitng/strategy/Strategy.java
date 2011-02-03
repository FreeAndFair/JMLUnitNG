/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.strategy;

import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * The interface for all test data generation strategies.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2010
 */
public interface Strategy {
  /**
   * To be implemented by users. Returns an iterator over the local-scope
   * values for this type.
   * 
   * @return What are your local-scope values?
   */
  RepeatedAccessIterator<?> localValues();

  /**
   * To be implemented by users. Returns an iterator over the class-scope 
   * values for this type.
   * 
   * @return What are your class-scope values?
   */
  RepeatedAccessIterator<?> classValues();

  /**
   * To be implemented by users. Returns an iterator over the package-scope
   * values for this type.
   * 
   * @return What are your package-scope values?
   */
  RepeatedAccessIterator<?> packageValues();
  
  /**
   * To be implemented by strategy classes. Returns the iterator over default 
   * values for this type.
   * 
   * @return What are your default values?
   */
  RepeatedAccessIterator<?> defaultValues();

  /**
   * Returns a RepeatedAccessIterator over all values.
   * 
   * @return What are all your values?
   */
  RepeatedAccessIterator<?> iterator();
}

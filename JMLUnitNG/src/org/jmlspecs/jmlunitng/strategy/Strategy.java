/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
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
   * To be implemented by strategy classes. Returns an iterator over the 
   * default values for this type.
   * 
   * @return What are your default values?
   */
  RepeatedAccessIterator<?> defaultValues();

  /**
   * Returns a RepeatedAccessIterator over the strategy values. This
   * iterator may contain all the various scoped values, or a fraction of
   * them chosen uniformly at random, as specified by configuration options. 
   * 
   * @return What are your values?
   */
  RepeatedAccessIterator<?> iterator();
}

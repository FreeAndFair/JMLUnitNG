/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "OpenJML"
 * @creation_date "March 2010"
 * @last_updated_date "March 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.iterator;

/**
 * An iterator that supports accessing the current value multiple times.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version March 2010
 * @param <T> The type of the returned elements.
 */
public interface RepeatedAccessIterator<T> {
  /** 
   * @return Does the iterator have a current element?
   */
  boolean hasElement();
  
  /**
   * @return What is the iterator's current element?
   */
  //@ requires hasElement();
  T element();
  
  /**
   * Advance the iterator to the next element!
   */
  //@ requires hasElement();
  void advance();
}

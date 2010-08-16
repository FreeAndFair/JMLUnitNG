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
   * @return True if the current element is valid, false if the iterator 
   * is past the end of the sequence.
   */
  boolean hasElement();
  
  /**
   * @return The current element of the iterator
   */
  //@ requires hasElement();
  T element();
  
  /**
   * Advances the iterator to the next element.
   */
  //@ requires hasElement();
  void advance();
}

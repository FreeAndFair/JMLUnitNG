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
  // Queries
  /**
   * 
   * @return True if the current element is valid. False if the iterator is past the end of the sequence.
   */
  boolean hasElement();
  
  /**
   * Returns the current element of the iterator. hasElement must return true for this call to be
   * valid.
   * @return The current element of the iterator
   */
  //@ requires hasElement();
  T element();
  // Commands
  
  /**
   * Advances the iterator to the next element.
   */
  // @constraint "The iterator cannot be advanced if it has no elements remaining."
  //@ requires hasElement();
  void advance();
}

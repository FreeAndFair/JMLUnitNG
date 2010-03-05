/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "OpenJML"
 * @creation_date "March 2010"
 * @last_updated_date "March 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.iterator;

/**
 * An iterator that supports accessing the current value multiple times.
 * 
 * @author Daniel M. Zimmerman
 * @version March 2010
 */
public interface RepeatedAccessIterator<T> {
  // Queries
	
  /**
   * @return Does the iterator have any elements remaining?
   */
  boolean hasMoreElements();
  
  /**
   * @return What is the current element of the iterator?
   */
  T element();
	
  // Commands
  
  /**
   * Advance the iterator to the next element!
   */
  // @constraint "The iterator cannot be advanced if it has no elements remaining."
  //@ requires hasMoreElements();
  void advance();
}

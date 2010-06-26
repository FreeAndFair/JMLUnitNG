/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "March 2010"
 * 
 * @last_updated_date "March 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.iterator;


/**
 * A repeated access iterator that iterates over an array of objects.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version March 2010
 */
public class ObjectArrayIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The list of iterator generation methods
   */
  private final T[] my_array;

  /**
   * The current element.
   */
  // @ invariant my_element <= my_array.length && my_element >= 0;
  private int my_element;

  /**
   * Creates a new ObjectArrayIterator that iterates over the given array
   * @param the_array The array of objects to iterate over.
   */
  /*@ ensures my_element == 0;
   */
  public ObjectArrayIterator(final T[] the_array) {
    my_array = the_array;
    my_element = 0;
  }

  /**
   * Advances the iterator to the next value.
   */
  //@ requires hasElement();
  public void advance() {
    my_element++;
  }

  /**
   * Returns the current element.
   */
  //@ requires hasElement();
  public T element() {
    return my_array[my_element];
  }

  /**
   * Returns true if there are more elements in this iterator. False if not.
   * @return True if there are more elements in this iterator. False if not.
   */
  //@ ensures \result == my_element < my_array.length;
  public boolean hasElement() {
  	return my_element < my_array.length;
  }

}

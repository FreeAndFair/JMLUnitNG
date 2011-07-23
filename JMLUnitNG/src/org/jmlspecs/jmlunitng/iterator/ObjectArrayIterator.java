/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

/**
 * A repeated access iterator that iterates over an array of objects.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version September 2010
 */
public class ObjectArrayIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The list of iterator generation methods.
   */
  private final T[] my_array;

  /**
   * The current element.
   */
  // @ private invariant my_element <= my_array.length && my_element >= 0;
  private int my_element;

  /**
   * Creates a new ObjectArrayIterator that iterates over the given array.
   * The array is <i>not</i> copied, so subsequent modifications to it will
   * affect the iteration.
   * 
   * @param the_array The array of objects to iterate over.
   */
  public ObjectArrayIterator(final /*@ non_null @*/ T[] the_array) {
    my_array = the_array;
    my_element = 0;
  }

  /**
   * {@inheritDoc}
   */
  public void advance() {
    my_element++;
  }

  /**
   * {@inheritDoc}
   */
  public T element() {
    return my_array[my_element];
  }

  /**
   * {@inheritDoc}
   */
  public boolean hasElement() {
    return my_element < my_array.length;
  }

}

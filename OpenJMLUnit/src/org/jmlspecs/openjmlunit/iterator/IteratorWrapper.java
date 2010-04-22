/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @author Jonathan Hogins
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.iterator;

import java.util.Iterator;

/**
 * Wraps a RepeatedAccessIterator in a standard Iterator.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 * @param <T> The type of object returned
 */
public class IteratorWrapper<T> implements Iterator<T> {
  /**
   * Is this iterator done?
   */
  private boolean my_is_done;
  /**
   * The RepeatedAccessIterator to wrap.
   */
  private final RepeatedAccessIterator<T> my_iterator;
  
  /**
   * Creates a new IteratorWrapper for the_iterator.
   * @param the_iterator The iterator to iterate over.
   */
  /*@ ensures my_iterator == the_iterator &&
    @         my_is_done == the_iterator.element() != null;
   */
  public IteratorWrapper(final RepeatedAccessIterator<T> the_iterator) {
    my_iterator = the_iterator;
    my_is_done = the_iterator.element() != null;
  }
  
  
  @Override
  public boolean hasNext() {
    return my_is_done;
  }

  /**
   * Returns the current element and increments the iterator.
   * @return The current element.
   */
  /*@ requires !my_is_done;
    @ ensures my_is_done == my_iterator.hasMoreElements();
   */
  @Override
  public T next() {
    final T result = my_iterator.element();
    if (my_iterator.hasMoreElements()) {
      my_iterator.advance();
    } else {
      my_is_done = true;
    }
    return result;
  }

  /**
   * Unsupported operation.
   * @throws UnsupportedOperationExcepton Always thrown.
   */
  /*@ signals (UnsupportedOperationException e) (true);
   */
  @Override
  public void remove() throws UnsupportedOperationException {
    throw new UnsupportedOperationException("No remove in RepeatedAccessIterator");
  }

}

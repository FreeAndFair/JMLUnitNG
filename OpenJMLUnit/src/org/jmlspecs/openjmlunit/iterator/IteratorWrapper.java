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
import java.util.NoSuchElementException;

/**
 * Wraps a RepeatedAccessIterator in a standard Iterator.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 * @param <T> The type of object returned
 */
public class IteratorWrapper<T> implements Iterator<T> {
  /**
   * The RepeatedAccessIterator to wrap.
   */
  private final RepeatedAccessIterator<T> my_iterator;
  
  /**
   * Creates a new IteratorWrapper for the_iterator.
   * @param the_iterator The iterator to iterate over.
   */
  /*@ ensures my_iterator == the_iterator;
   */
  public IteratorWrapper(final RepeatedAccessIterator<T> the_iterator) {
    my_iterator = the_iterator;
  }
  
  
  @Override
  public boolean hasNext() {
    return my_iterator.hasElement();
  }

  /**
   * Returns the current element and increments the iterator.
   * @return The current element.
   */
  @Override
  public T next() {
    if (!hasNext()) {
      throw new NoSuchElementException();
    }
    final T result = my_iterator.element();
    my_iterator.advance();
    return result;
  }

  /**
   * Unsupported operation.
   * @throws UnsupportedOperationExcepton Always thrown.
   */
  /*@ signals (UnsupportedOperationException e) (true); */
  @Override
  public void remove() throws UnsupportedOperationException {
    throw new UnsupportedOperationException("No remove in RepeatedAccessIterator");
  }

}

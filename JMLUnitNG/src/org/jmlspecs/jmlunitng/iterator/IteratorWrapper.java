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

package org.jmlspecs.jmlunitng.iterator;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Wraps a RepeatedAccessIterator in a standard Iterator.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version September 2010
 * @param <T> The type of object returned
 */
public class IteratorWrapper<T> implements Iterator<T> {
  /**
   * The RepeatedAccessIterator to wrap.
   */
  private final RepeatedAccessIterator<T> my_iterator;
  
  /**
   * Creates a new IteratorWrapper for the_iterator.
   * 
   * @param the_iterator The iterator to wrap.
   */
  public IteratorWrapper(final /*@ non_null @*/ RepeatedAccessIterator<T> the_iterator) {
    my_iterator = the_iterator;
  }
  
  /**
   * {@inheritDoc}
   */
  @Override
  public boolean hasNext() {
    return my_iterator.hasElement();
  }

  /**
   * {@inheritDoc}
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
   * 
   * @throws UnsupportedOperationExcepton always.
   */
  //@ signals UnsupportedOperationException true;
  //@ signals_only UnsupportedOperationException;
  @Override
  public void remove() throws UnsupportedOperationException {
    throw new UnsupportedOperationException
    ("RepeatedAccessIterator does not support the remove operation.");
  }
}

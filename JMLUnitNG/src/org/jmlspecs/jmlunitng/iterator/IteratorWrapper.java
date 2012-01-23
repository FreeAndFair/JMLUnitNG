/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Wraps a RepeatedAccessIterator in a standard Iterator.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version July 2011
 * @param <T> The type of the returned elements.
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
      throw new NoSuchElementException("iterator has no next element");
    }
    final T result = my_iterator.element();
    my_iterator.advance();
    return result;
  }

  /**
   * Unsupported operation.
   * 
   * @throws UnsupportedOperationException always.
   */
  //@ signals UnsupportedOperationException true;
  //@ signals_only UnsupportedOperationException;
  @Override
  public void remove() throws UnsupportedOperationException {
    throw new UnsupportedOperationException
    (my_iterator.getClass().getName() + " does not support the remove operation.");
  }
  
  /**
   * @return the wrapped iterator. This returns the actual wrapped iterator
   * instance in whatever state it is in, and should therefore be used with care.
   */
  public RepeatedAccessIterator<T> wrapped() {
    return my_iterator;
  }
}

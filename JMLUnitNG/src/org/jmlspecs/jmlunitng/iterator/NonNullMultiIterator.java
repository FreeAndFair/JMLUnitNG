/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.List;

/**
 * A repeated access iterator that combines one or more other iterators, 
 * and eliminates as many <code>null</code> values as it can (the last
 * value read may still be null).
 * 
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public class NonNullMultiIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The Iterator over concatenated iterators.
   */
  private final IteratorAdapter<RepeatedAccessIterator<T>> my_iterators;

  /**
   * Creates a new MultiIterator that iterates over all given iterators in
   * sequence.
   * 
   * @param iterators The list of iterators to iterate over.
   */
  public NonNullMultiIterator(final List<RepeatedAccessIterator<T>> the_iterators) {
    my_iterators =
      new IteratorAdapter<RepeatedAccessIterator<T>>(the_iterators.iterator());
    // advance to the first non-null element
    if (!hasElement()) {
      advance();
    }
  }

  /**
   * Advances the multi-iterator to the next non-null value, if one exists.
   */
  @Override
  public final void advance() {
    advanceCurrentIterator();
    while (my_iterators.hasElement() && !my_iterators.element().hasElement()) {
      // we ran out of elements in current iterator, so go on to next one
      my_iterators.advance();
      advanceCurrentIterator();
    }
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public /*@ pure */ T element() {
    return my_iterators.element().element();
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public /*@ pure */ boolean hasElement() {
    return my_iterators.hasElement() && 
           my_iterators.element().hasElement() &&
           my_iterators.element().element() != null;
  }

  /**
   * Advances the current iterator of the multi-iterator, until we reach
   * a non-null value or the end.
   */
  private void advanceCurrentIterator() {
    if (my_iterators.hasElement() && my_iterators.element() != null &&
        my_iterators.element().hasElement()) {
      do {
        my_iterators.element().advance();
      }
      while (my_iterators.element().hasElement() &&
             my_iterators.element().element() == null);
    }
  }
}

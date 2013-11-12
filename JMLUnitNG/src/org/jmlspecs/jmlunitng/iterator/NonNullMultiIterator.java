/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

/**
 * A repeated access iterator that combines one or more other iterators, 
 * and eliminates as many <code>null</code> values as it can (the last
 * value read may still be null).
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 * @param <T> The type of the returned elements.
 */
public class NonNullMultiIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The Iterator over concatenated iterators.
   */
  private final RepeatedAccessIterator<RepeatedAccessIterator<T>> my_iterators;

  /**
   * Creates a new MultiIterator that iterates over all given iterators in
   * sequence.
   * 
   * @param the_iterators The list of iterators to iterate over.
   */
  @SuppressWarnings("unchecked")
  public NonNullMultiIterator(final List<RepeatedAccessIterator<T>> the_iterators) {
    // only keep non-empty iterators
    final List<RepeatedAccessIterator<T>> non_empties = 
      new LinkedList<RepeatedAccessIterator<T>>();
    for (RepeatedAccessIterator<T> i : the_iterators) {
      if (i.hasElement()) {
        non_empties.add(i);
      }
    }
    final RepeatedAccessIterator<T>[] non_empty_array = 
        non_empties.toArray(new RepeatedAccessIterator[non_empties.size()]);
    my_iterators = 
      new ObjectArrayIterator<RepeatedAccessIterator<T>>(non_empty_array);
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
      if (!hasElement()) {
        advanceCurrentIterator();
      }
    }
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public /*@ pure */ T element() throws NoSuchElementException {
    return my_iterators.element().element();
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public final /*@ pure */ boolean hasElement() {
    boolean result = false;
    if (my_iterators.hasElement()) {
      try {
        result = my_iterators.element().element() != null;
      } catch (final NoSuchElementException e) {
        // optimization to help prevent unnecessary instantiation
        result = false;
      }
    }
    return result;
    /*  // original code
    return my_iterators.hasElement() && 
           my_iterators.element().hasElement() &&
           my_iterators.element().element() != null;
    */
  }

  /**
   * Advances the current iterator of the multi-iterator, until we reach
   * a non-null value or the end.
   */
  private void advanceCurrentIterator() {
    try {
      final RepeatedAccessIterator<T> iter = my_iterators.element();
      if (iter != null) {
        T element;
        do {
          iter.advance();
          element = iter.element();
        } while (element == null);
      }
    } catch (final NoSuchElementException e) {
      // we hit the end
      // (optimization to help prevent unnecessary instantiations)
    }
    /*  // original code
    if (my_iterators.hasElement() && my_iterators.element() != null &&
        my_iterators.element().hasElement()) {
      do {
        my_iterators.element().advance();
      } 
      while (my_iterators.element().hasElement() &&
             my_iterators.element().element() == null);
    }
    */
  }
}

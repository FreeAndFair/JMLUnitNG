/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.LinkedList;
import java.util.List;

/**
 * A repeated access iterator that combines one or more other iterators.
 * 
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public class MultiIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The Iterator over concatenated iterators.
   */
  private final IteratorAdapter<RepeatedAccessIterator<T>> my_iterators;

  /**
   * Creates a new MultiIterator that iterates over all given iterators in
   * sequence.
   * 
   * @param the_iterators The list of iterators to iterate over.
   */
  public MultiIterator(final List<RepeatedAccessIterator<T>> the_iterators) {
    // only keep non-empty iterators
    final List<RepeatedAccessIterator<T>> non_empties = 
      new LinkedList<RepeatedAccessIterator<T>>();
    for (RepeatedAccessIterator<T> i : the_iterators) {
      if (i.hasElement()) {
        non_empties.add(i);
      }
    }
    my_iterators = 
      new IteratorAdapter<RepeatedAccessIterator<T>>(non_empties.iterator());
    // at this point, the iterator either has an element or is completely empty
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public final void advance() {
    if (my_iterators.hasElement() && my_iterators.element().hasElement()) {
      my_iterators.element().advance();
    }
    while (my_iterators.hasElement() && 
           !my_iterators.element().hasElement()) {
      my_iterators.advance();
    }
    // at this point, the iterator either has an element or is completely empty, 
    // as all the individual iterators are non-empty.
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
           my_iterators.element().hasElement();
  }
}

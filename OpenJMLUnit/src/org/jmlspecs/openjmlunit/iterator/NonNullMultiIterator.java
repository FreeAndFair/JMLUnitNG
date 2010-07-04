/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "OpenJML"
 * @creation_date "March 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.iterator;

import java.util.List;

/**
 * A repeated access iterator that combines one or more other iterators, 
 * and eliminates as many <code>null</code> values as it can (the last
 * value read may be null).
 * 
 * @author Daniel M. Zimmerman
 * @version July 2010
 */
public class NonNullMultiIterator<T> implements RepeatedAccessIterator<T> {
  // Commands

  // @command "Embed the_list_of_iterators into a single iterator!"

  // Constraints

  // @constraint "The sequence of elements returned is exactly the
  //              concatenation of the sequences of elements returned by
  //              the iterators in the iterator list, in the order they
  //              appear in the list."

  /**
   * The Iterator over concatenated iterators.
   */
  private IteratorAdapter<RepeatedAccessIterator<T>> my_current_iterator;

  /**
   * Creates a new MultiIterator that iterates over all given iterators in
   * sequence.
   * 
   * @param iterators The list of iterators to iterate over.
   */
  public NonNullMultiIterator(List<RepeatedAccessIterator<T>> the_iterators) {
    my_current_iterator = new IteratorAdapter<RepeatedAccessIterator<T>>(the_iterators.iterator());
    // advance to the next non-null element
    while (my_current_iterator.hasElement() && 
           (my_current_iterator.element() == null || 
            !my_current_iterator.element().hasElement())) {
      my_current_iterator.advance();
      while (my_current_iterator.element() != null && 
             my_current_iterator.element().hasElement() &&
             my_current_iterator.element().element() == null)
      {
        my_current_iterator.element().advance();
      }
    }
  }

  /**
   * Advances the MultiIterator to the next value in the sequence.
   */
  /*@ requires hasElement(); */
  @Override
  public void advance() {
    internalAdvance();
  }

  /**
   * Returns the current element in the sequence.
   * 
   * @return The current element.
   */
  //@ requires hasElement();
  @Override
  public /*@ pure */ T element() {
    return my_current_iterator.element().element();
  }

  /**
   * @inheritDoc
   */
  @Override
  public /*@ pure */ boolean hasElement() {
    return my_current_iterator.hasElement() && 
           my_current_iterator.element().hasElement();
  }

  /**
   * Helper method for advancing to the next element. Allows the internal
   * advance method to be called from the constructor while allowing the public
   * advance() to be non-final.
   */
  /*@ requires hasElement(); */
  private void internalAdvance() {
    if (my_current_iterator.hasElement() && my_current_iterator.element() != null &&
        my_current_iterator.element().hasElement()) {
      do
      {
        my_current_iterator.element().advance();
      }
      while (my_current_iterator.element().element() == null && my_current_iterator.element().hasElement());
    }
    //proceed in the sequence until the first element is found or the end is reached.
    while (my_current_iterator.hasElement() && !my_current_iterator.element().hasElement()) {
      my_current_iterator.advance();
      while (my_current_iterator.element() != null && 
             my_current_iterator.element().hasElement() &&
             my_current_iterator.element().element() == null)
      {
        my_current_iterator.element().advance();
      }
    }
  }
}

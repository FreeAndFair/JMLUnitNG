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

import java.util.Iterator;
import java.util.List;

/**
 * A repeated access iterator that combines one or more other iterators.
 * 
 * @author Daniel M. Zimmerman
 * @version March 2010
 */
public class MultiIterator implements RepeatedAccessIterator {
  // Commands
  
  // @command "Embed the_list_of_iterators into a single iterator!"
  
  // Constraints
  
  // @constraint "The sequence of elements returned is exactly the
  //              concatenation of the sequences of elements returned by
  //              the iterators in the iterator list, in the order they
  //              appear in the list."
  
  /* @ public invariant my_iterators.contains(my_current_iterator) || 
         my_current_iterator == null */
  
  /**
   * The list of Iterators to be concatenated.
   */
  private final List<Iterator<?>> my_iterators;
  /**
   * The Iterator over my_iterators.
   */
  private IteratorAdapter<Iterator<?>> my_current_iterator;
  
  /**
   * The current element in the sequence
   */
  /* @ nullable */
  private Object my_current_element;
  
  /*@ requires !the_iterators.isEmpty() &&
    @         (/forall Iterator<?> i; the_iterators.contains(i); i.hasNext()) 
    @*/
  public MultiIterator(List<Iterator<?>>  the_iterators) {
    my_iterators = the_iterators;
    my_current_iterator = new IteratorAdapter<Iterator<?>>(the_iterators.iterator());
    internalAdvance();
  }

  /**
   * Advances the MultiIterator to the next value in the sequence.
   */
  /* @ requires hasMoreElements()
  */
  @Override
  public void advance() {
    internalAdvance();
  }

  @Override
  /* @ pure */
  public Object element() {
    return my_current_element;
  }

  @Override
  /* @ pure */
  public boolean hasMoreElements() {
    return my_current_iterator.element() != null && 
      (my_current_iterator.element().hasNext() || my_current_iterator.hasMoreElements());
  }
  
  /**
   * Helper method for advancing to the next element. Allows the internal advance method
   * to be called from the constructor while allowing the public advance() to be 
   * non-final.
   */
  /* @ helper
   * @ requires hasMoreElements()
  */
  private final void internalAdvance() {
    //proceed in the sequence until the first element is found or the end is reached.
    while (!my_current_iterator.element().hasNext() && 
        my_current_iterator.hasMoreElements()) {
      my_current_iterator.advance();
    }
    if (my_current_iterator.element().hasNext())
      my_current_element = my_current_iterator.element().next();
  }
}

/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @author Jonathan Hogins
 * 
 * @module "OpenJML"
 * 
 * @creation_date "March 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.Iterator;

/**
 * An adapter that turns a standard Java iterator into a repeated access
 * iterator.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version April 2010
 * @param <T> The type of the returned elements.
 */
public class IteratorAdapter<T> implements RepeatedAccessIterator<T> {
  /**
   * The embedded iterator.
   */
  private final Iterator<T> my_iterator;

  /**
   * The current element of the embedded iterator.
   */
  private T my_current;
  
  /**
   * Is this iterator on a valid element?
   */
  private boolean my_is_valid;

  /**
   * Embed the_java_util_iterator into a repeated access iterator!
   * 
   * @param the_java_util_iterator The iterator to embed.
   */
  // @constraint "The embedded iterator must be non-null."
  public IteratorAdapter(final/*@ non_null @*/Iterator<T> the_java_util_iterator) {
    my_iterator = the_java_util_iterator;
    if (my_iterator.hasNext()) {
      my_current = my_iterator.next();
      my_is_valid = true;
    } else {
      my_is_valid = false;
    }
  }

  // Interface Methods

  /**
   * @return Does the iterator have any elements remaining?
   */
  public boolean hasElement() {
    return my_is_valid;
  }

  /**
   * @return What is the current element of the iterator?
   */
  public T element() {
    return my_current;
  }

  /**
   * Advance the iterator to the next element!
   */
  public void advance() {
    if (my_iterator.hasNext()) {
      my_current = my_iterator.next();
    } else {
      my_is_valid = false;
    }
  }
}

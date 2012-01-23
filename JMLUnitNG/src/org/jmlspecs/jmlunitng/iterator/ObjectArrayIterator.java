/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.NoSuchElementException;

import org.jmlspecs.jmlunitng.objgen.ObjectGenerator;

/**
 * A repeated access iterator that iterates over an array of objects. 
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version January 2012
 * @param <T> The type of the returned elements.
 */
public class ObjectArrayIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The list of iterator generation methods.
   */
  private final Object[] my_array;

  /**
   * The current element.
   */
  // @ private invariant my_element <= my_array.length && my_element >= 0;
  private int my_element;

  /**
   * Creates a new ObjectArrayIterator that iterates over the given array.
   * The array is <i>not</i> copied, so subsequent modifications to it will
   * affect the iteration.
   * 
   * @param the_array The array of objects to iterate over.
   */
  public ObjectArrayIterator(final /*@ non_null @*/ T[] the_array) {
    my_array = the_array;
    my_element = 0;
  }

  /**
   * Creates a new ObjectArrayIterator that iterates over the given array.
   * The array is <i>not</i> copied, so subsequent modifications to it will
   * affect the iteration.
   * 
   * @param the_class The class of the objects in the iterator. This class 
   * must be assignable to class T.
   * @param the_array The array of objects and object generators to iterate over.
   * @exception ClassCastException if any object in the array is not
   * castable to the_class or an object generator that generates objects  
   * castable to the_class.
   */
  public ObjectArrayIterator(final Class<T> the_class, 
                             final /*@ non_null @*/ Object[] the_array) 
    throws ClassCastException {
    checkClasses(the_class, the_array);
    my_array = the_array;
    my_element = 0;
  }
  
  /**
   * Checks to see whether all the elements of the_array are instances of
   * the_class (or a descendant) or generators for such instances. 
   * 
   * @param the_class The class to check.
   * @param the_array The array to check.
   * @exception ClassCastException if any object in the array is not
   * castable to the_class or an object generator that generates objects  
   * castable to the_class.
   */
  private void checkClasses(final Class<T> the_class, 
                            final /*@ non_null @*/ Object[] the_array) {
    for (final Object o : the_array) {
      boolean legal_class = the_class.isAssignableFrom(o.getClass());
      if (!legal_class && ObjectGenerator.class.isAssignableFrom(o.getClass())) {
        final ObjectGenerator generator = (ObjectGenerator) o;
        legal_class = the_class.isAssignableFrom(generator.generatedClass());
      }
      if (!legal_class) {
        throw new ClassCastException("cannot assign object " + o + 
                                     " to class " + the_class);
      }
    }
  }
  
  /**
   * {@inheritDoc}
   */
  public void advance() {
    my_element++;
  }

  /**
   * {@inheritDoc}
   */
  @SuppressWarnings("unchecked")
  public T element() throws NoSuchElementException {
    if (!hasElement()) {
      throw new NoSuchElementException("iterator has no current element");
    }
    Object result = my_array[my_element];
    if (result instanceof ObjectGenerator) {
      try {
        result = ((ObjectGenerator) result).generate();
      } catch (Exception e) { // TODO make this more specific
        result = null;
      }
    } // else result instanceof T, because of checkClasses() at construction
    return (T) result;
  }

  /**
   * {@inheritDoc}
   */
  public boolean hasElement() {
    return my_element < my_array.length;
  }

}

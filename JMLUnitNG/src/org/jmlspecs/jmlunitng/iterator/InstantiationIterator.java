/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

import java.lang.reflect.Constructor;
import java.util.NoSuchElementException;


/**
 * A repeated access iterator that instantiates objects of a 
 * specific class using an iterator of parameter lists and signatures.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 * @param <T> The type of the returned elements.
 */
public class InstantiationIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The parameter types of the constructor to use.
   */
  private final Constructor<T> my_constructor;
  
  /**
   * The iterator of parameter lists.
   */
  private final RepeatedAccessIterator<Object[]> my_params;

  /**
   * Creates a new InstantiationIterator that iterates over the given
   * parameter list and attempts to instantiate the specified class
   * using a constructor for each set of parameters.
   * 
   * @param the_class The class to instantiate.
   * @param the_param_types The types of the parameters.
   * @param the_params The iterator of parameter lists.
   */
  public InstantiationIterator(final Class<T> the_class, 
                               final Class<?>[] the_param_types,
                               final RepeatedAccessIterator<Object[]> the_params) {
    Constructor<T> c;
    try {
      c = the_class.getConstructor(the_param_types);
    } catch (final NoSuchMethodException e) {
      c = null;
    }
    my_constructor = c;
    my_params = the_params;
  }

  /**
   * {@inheritDoc}
   */
  public void advance() {
    // since not all parameter lists will in fact give valid
    // values, we advance to the next valid value by checking
    // element(), at least until we hit the end
    boolean not_finished;
    do {
      my_params.advance();
      // an optimization to prevent unnecessary instantiation
      try {
        not_finished = element() == null;
      } catch (final NoSuchElementException e) {
        not_finished = false;
      }
    } while (not_finished);
  }
  
  /**
   * {@inheritDoc}
   */
  public T element() throws NoSuchElementException {
    if (my_constructor == null) {
      throw new NoSuchElementException("no valid constructor exists");
    }
    // for whatever the current parameter list is, we attempt
    // to find a constructor
    T result = null;
    
    try {
      final Object[] param_list = my_params.element();
      result = my_constructor.newInstance(param_list);
    } catch (final NoSuchElementException e) {
      throw e;
    } catch (final Exception e) {
      // normally we wouldn't catch "Exception", but in this case,
      // no matter what went wrong with the instantiation, we need 
      // to do the same thing: return null
      result = null;
    }

    return result;
  }

  /**
   * {@inheritDoc}
   */
  public boolean hasElement() {
    return my_params.hasElement();
  }
}

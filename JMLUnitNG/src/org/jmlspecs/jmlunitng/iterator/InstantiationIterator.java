/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.iterator;

import java.lang.reflect.Constructor;
import java.util.HashSet;
import java.util.Set;


/**
 * A repeated access iterator that instantiates objects of a 
 * specific class using an iterator of parameter lists and signatures.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
 * @param <T> The type of the returned elements.
 */
public class InstantiationIterator<T> implements RepeatedAccessIterator<T> {
  /**
   * The class object for the class we are instantiating.
   */
  private final Class<T> my_class;
  
  /**
   * The parameter types of the constructor to use.
   */
  private final Class<?>[] my_param_types;
  
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
    my_class = the_class;
    my_param_types = the_param_types;
    my_params = the_params;
  }

  /**
   * {@inheritDoc}
   */
  public void advance() {
    // since not all parameter lists will in fact give valid
    // values, we advance to the next valid value by checking
    // element(), at least until we hit the end
    do {
      my_params.advance();
    } while (hasElement() && element() == null);
  }

  private Set<Object> seen = new HashSet<Object>();
  
  /**
   * {@inheritDoc}
   */
  public T element() {
    // for whatever the current parameter list is, we attempt
    // to find a constructor
    T result = null;
    
    try {
      final Object[] param_list = my_params.element();
      final Constructor<T> c = my_class.getConstructor(my_param_types);
      result = c.newInstance(param_list);
    } catch (final Exception e) {
      // normally we wouldn't catch "Exception", but in this case,
      // no matter what went wrong, we need to do the same thing,
      // namely return null
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

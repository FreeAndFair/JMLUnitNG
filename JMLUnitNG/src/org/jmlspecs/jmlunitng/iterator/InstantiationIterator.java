/*
 * OpenJMLUnit
 *
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "OpenJML"
 * @creation_date "March 2010"
 * @last_updated_date "March 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.iterator;

import java.lang.reflect.Constructor;


/**
 * A repeated access iterator that instantiates objects of a 
 * specific class using an iterator of parameter lists and signatures.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2010
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
   * @param the_param_lists The iterator of parameter lists.
   */
  public InstantiationIterator(final Class<T> the_class, 
                               final Class<?>[] the_param_types,
                               final RepeatedAccessIterator<Object[]> the_params) {
    my_class = the_class;
    my_param_types = the_param_types;
    my_params = the_params;
  }

  /**
   * Advances the iterator to the next value.
   */
  //@ requires hasElement();
  public void advance() {
    // since not all parameter lists will in fact give valid
    // values, we advance to the next valid value by checking
    // element(), at least until we hit the end
    
    do {
      my_params.advance();
    } while (element() == null && hasElement());
  }

  /**
   * Returns the current element.
   */
  //@ requires hasElement();
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
   * Returns true if there are more elements in this iterator. False if not.
   * @return True if there are more elements in this iterator. False if not.
   */
  public boolean hasElement() {
  	return my_params.hasElement();
  }
}
/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.iterator;

import org.jmlspecs.jmlunitng.strategy.Strategy;

/**
 * A repeated access iterator that generates arrays of objects by reflectively
 * instantiating iterator classes that contain test parameter data.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version September 2010
 */
public class ParameterArrayIterator implements RepeatedAccessIterator<Object[]> {
  /**
   * The list of iterator generation methods
   */
  private final Class<? extends Strategy>[] my_strategy_classes;
  
  /**
   * The current strategies being used.
   */
  //@ private invariant my_strategies.length == my_strategy_classes.length;
  private RepeatedAccessIterator<?>[] my_strategies;

  /**
   * The current element (i.e., parameter array).
   */
  //@ private invariant my_element.length == my_strategies.length;
  private Object[] my_element;
  
  /**
   * A flag indicating whether there are elements remaining.
   */
  private boolean my_is_finished;

  /**
   * Creates a new ObjectArrayIterator that iterates over all combinations of objects
   * in the given Strategy classes.
   * 
   * @param the_strategy_classes The strategies to iterate over.
   * @throws IllegalArgumentException if there is a problem calling the constructors
   * of the strategy classes.
   */
  /*@ requires (\forall int i; i >= 0 && i < the_strategy_classes.length; 
    @		the_strategy_classes[i].newInstance().iterator().hasElement());
    @*/
  public ParameterArrayIterator(final Class<? extends Strategy>... the_strategy_classes) {
  	my_strategy_classes = the_strategy_classes;
  	my_strategies = new RepeatedAccessIterator<?>[the_strategy_classes.length];
  	my_is_finished = the_strategy_classes.length == 0;
  	my_element = new Object[my_strategies.length];
  	for (int i = 0; i < my_strategies.length; i++) {
  		try {
				my_strategies[i] = the_strategy_classes[i].newInstance().iterator();
				if (my_strategies[i].hasElement()) {
				  my_element[i] = my_strategies[i].element();
				} // else the element stays at its default value of null
			} catch (InstantiationException e) {
				throw new IllegalArgumentException(e);
			} catch (IllegalAccessException e) {
				throw new IllegalArgumentException(e);
			}
  	}
	}

  /**
   * {@inheritDoc}
   */
  public Object[] element() {
    return my_element;
  }

  /**
   * {@inheritDoc}
   */
  public boolean hasElement() {
  	return !my_is_finished;
  }
  
  /**
   * {@inheritDoc}
   */
  //@ requires hasElement();
  public void advance() {
		try {
	    int p = 0;
			while (p < my_strategies.length) {
		    // ensure each iterator is at a valid element
				my_strategies[p].advance();
				if (my_strategies[p].hasElement()) {
  				// no need to check the other iterators
					break; 
				} else {
					my_strategies[p] = 
					  (RepeatedAccessIterator<?>) my_strategy_classes[p].newInstance().iterator();
		      p++;
				}
			} 
			my_element = new Object[my_strategies.length];
			for (int i = 0; i < my_strategies.length; i++) {
				if (my_strategies[i].hasElement()) {
				  my_element[i] = my_strategies[i].element();
				} else {
				  my_element[i] = null;
				}
			}
			// if we've reset the last iterator, we're done
			my_is_finished = p == my_strategies.length;
		} catch (InstantiationException e) {
			// this should never happen because we checked them earlier
			System.err.println(e);
		} catch (IllegalAccessException e) {
		  // neither should this
			System.err.println(e);
		}
  }
}

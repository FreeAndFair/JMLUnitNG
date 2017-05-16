/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.iterator;

import java.util.NoSuchElementException;
import java.util.Random;

/**
 * A wrapper that encapsulates a RepeatedAccessIterator and provides a random
 * sample of its elements, based on a specified random seed and a fraction
 * of elements to return. Because iterators are evaluated lazily, the
 * fraction of elements actually returned is imprecise (it is closest to
 * the specified fraction for iterators with many elements). The first element
 * of the underlying iterator is always returned regardless of the fraction.
 * 
 * @author Daniel M. Zimmerman
 * @param <T> The type to be sampled.
 * @version February 2011
 */
public class IteratorSampler<T> implements RepeatedAccessIterator<T> {
  /**
   * The underlying RepeatedAccessIterator.
   */
  private final RepeatedAccessIterator<T> my_iterator;
  
  /**
   * The fraction of iterator elements to provide.
   */
  private final double my_fraction;
  
  /**
   * The random number generator used by this IteratorSampler.
   */
  private final Random my_random;
  
  /**
   * Constructs an IteratorSampler for the specified iterator with the
   * specified parameters. The fraction must be greater than 0 to be 
   * meaningful, though negative values will still work (they result
   * in only the last element of the underlying iterator being returned).
   *
   * @param the_iterator The iterator to sample.
   * @param the_fraction The fraction of values to return from the iterator.
   * @param the_seed The random seed to use (for reproducibility of results).
   */
  public IteratorSampler(final RepeatedAccessIterator<T> the_iterator, 
                         final double the_fraction, final long the_seed) {
    my_iterator = the_iterator;
    my_fraction = the_fraction;
    my_random = new Random(the_seed);
  }
  
  /**
   * {@inheritDoc}
   */
  @Override
  public /*@ pure */ T element() throws NoSuchElementException {
    return my_iterator.element();
  }
   
  /**
   * {@inheritDoc}
   */
  @Override
  public final /*@ pure */ boolean hasElement() {
    return my_iterator.hasElement();
  }
  
  /**
   * Advances the iterator to the next selected value, or the last value if
   * no value is selected before the last value.
   */
  @Override
  public void advance() {
    my_iterator.advance();
    // now comes the random part; we skip this new element, and subsequent
    // elements, for as long as we generate random numbers > my_fraction.
    while (my_iterator.hasElement() && my_random.nextDouble() > my_fraction) {
      my_iterator.advance();
    }
  }
}

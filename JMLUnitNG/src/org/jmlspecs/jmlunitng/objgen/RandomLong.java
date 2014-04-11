/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.objgen;

import java.util.Random;

/**
 * A generator that uses a random number generator (with an optionally specified
 * seed) to provide fresh long integers within a specified range.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 */
public class RandomLong implements ObjectGenerator<Long> {
  /**
   * The random number generator used by this RandomInteger.
   */
  private final Random my_random;
  
  /**
   * The minimum integer to generate, inclusive.
   */
  private final long my_minimum;
  
  /**
   * The maximum integer to generate, exclusive.
   */
  private final long my_maximum;
  
  /**
   * Constructs a new RandomLong to generate random long integers between
   * the given minimum value (inclusive) and maximum value (exclusive).
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomLong(final long the_minimum, final long the_maximum) 
    throws IllegalArgumentException {
    this(the_minimum, the_maximum, Double.doubleToLongBits(Math.random()));
  }
  
  /**
   * Constructs a new RandomLong to generate random long integers between
   * the given minimum value (inclusive) and maximum value (exclusive), 
   * using the specified random seed.
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @param the_seed The random seed.
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomLong(final long the_minimum, final long the_maximum, 
                    final long the_seed) 
    throws IllegalArgumentException {
    if (the_maximum <= the_minimum) {
      throw new IllegalArgumentException(the_maximum + " <= " + the_minimum);
    }
    my_random = new Random(the_seed);
    my_minimum = the_minimum;
    my_maximum = the_maximum;
  }
  
  @Override
  public Long generate() {
    // algorithm from nextLong() methods of java.util.concurrent.ThreadLocalRandom
    long range = my_maximum - my_minimum;
    long offset = 0;
    while (range >= Integer.MAX_VALUE) {
      final int bits = my_random.nextInt(4); // next(2)
      final long half = range >>> 1;
      long next_range = half;
      if ((bits & 2) != 0) {
        next_range = range - half;
      }
      if ((bits & 1) == 0) {
        offset = offset + (range - next_range);
      }
      range = next_range;
    }
    return my_minimum + offset + my_random.nextInt((int) range);
  }

  @Override
  public Class<?> generatedClass() {
    return Long.class;
  }
}

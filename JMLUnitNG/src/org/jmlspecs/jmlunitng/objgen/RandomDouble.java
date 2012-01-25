/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.objgen;

import java.util.Random;

/**
 * A generator that uses a random number generator (with an optionally specified
 * seed) to provide fresh doubles within a specified range.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 */
public class RandomDouble implements ObjectGenerator<Double> {
  /**
   * The random number generator used by this RandomDouble.
   */
  private final Random my_random;
  
  /**
   * The minimum double to generate, inclusive.
   */
  private final double my_minimum;
  
  /**
   * The maximum double to generate, exclusive.
   */
  private final double my_maximum;
  
  /**
   * Constructs a new RandomDouble to generate random doubles between
   * the given minimum value (inclusive) and maximum value (exclusive).
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomDouble(final double the_minimum, final double the_maximum) 
    throws IllegalArgumentException {
    this(the_minimum, the_maximum, Double.doubleToLongBits(Math.random()));
  }
  
  /**
   * Constructs a new RandomDouble to generate random doubles between
   * the given minimum value (inclusive) and maximum value (exclusive), 
   * using the specified random seed.
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @param the_seed The random seed.
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomDouble(final double the_minimum, final double the_maximum, 
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
  public Double generate() {
    return my_random.nextDouble() * (my_maximum - my_minimum) + my_minimum;
  }

  @Override
  public Class<?> generatedClass() {
    return Double.class;
  }
}

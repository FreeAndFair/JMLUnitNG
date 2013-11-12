/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.objgen;

import java.util.Random;

/**
 * A generator that uses a random number generator (with an optionally specified
 * seed) to provide fresh bytes within a specified range.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 */
public class RandomByte implements ObjectGenerator<Byte> {
  /**
   * The random number generator used by this RandomByte.
   */
  private final Random my_random;
  
  /**
   * The minimum byte to generate, inclusive.
   */
  private final byte my_minimum;
  
  /**
   * The maximum byte to generate, exclusive.
   */
  private final byte my_maximum;
  
  /**
   * Constructs a new RandomByte to generate random bytes between
   * the given minimum value (inclusive) and maximum value (exclusive).
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomByte(final byte the_minimum, final byte the_maximum) 
    throws IllegalArgumentException {
    this(the_minimum, the_maximum, Double.doubleToLongBits(Math.random()));

  }
  
  /**
   * Constructs a new RandomByte to generate random bytes between
   * the given minimum value (inclusive) and maximum value (exclusive), 
   * using the specified random seed.
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @param the_seed The random seed.
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomByte(final byte the_minimum, final byte the_maximum, 
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
  public Byte generate() {
    return (byte) (my_random.nextInt(my_maximum - my_minimum) + my_minimum);
  }

  @Override
  public Class<?> generatedClass() {
    return Byte.class;
  }
}

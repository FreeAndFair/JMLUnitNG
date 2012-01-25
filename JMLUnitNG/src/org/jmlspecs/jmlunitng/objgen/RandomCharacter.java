/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.objgen;

import java.util.Random;

/**
 * A generator that uses a random number generator (with an optionally specified
 * seed) to provide fresh chars within a specified range.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 */
public class RandomCharacter implements ObjectGenerator<Character> {
  /**
   * The random number generator used by this RandomCharacter.
   */
  private final Random my_random;
  
  /**
   * The minimum char to generate, inclusive.
   */
  private final char my_minimum;
  
  /**
   * The maximum char to generate, exclusive.
   */
  private final char my_maximum;
  
  /**
   * Constructs a new RandomCharacter to generate random chars between
   * the given minimum value (inclusive) and maximum value (exclusive).
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomCharacter(final char the_minimum, final char the_maximum) 
    throws IllegalArgumentException {
    this(the_minimum, the_maximum, Double.doubleToLongBits(Math.random()));
  }
  
  /**
   * Constructs a new RandomCharacter to generate random chars between
   * the given minimum value (inclusive) and maximum value (exclusive), 
   * using the specified random seed.
   * 
   * @param the_minimum The minimum value to generate (inclusive).
   * @param the_maximum The maximum value to generate (exclusive).
   * @param the_seed The random seed.
   * @exception IllegalArgumentException if the maximum value is less
   * than or equal to the minimum value.
   */
  public RandomCharacter(final char the_minimum, final char the_maximum, 
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
  public Character generate() {
    return (char) (my_random.nextInt(my_maximum - my_minimum) + my_minimum);
  }

  @Override
  public Class<?> generatedClass() {
    return Character.class;
  }
}

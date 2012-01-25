/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.objgen;

import java.util.Random;

/**
 * A generator that uses a random number generator (with an optionally specified
 * seed) to provide fresh integers within a specified range.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 */
public class RandomString implements ObjectGenerator<String> {
  /**
   * The minimum printable character.
   */
  private static final char MIN_PRINTABLE = 32;
  
  /**
   * The maximum printable character.
   */
  private static final char MAX_PRINTABLE = 126;
  
  /**
   * The random number generator used by this RandomString.
   */
  private final Random my_random;
  
  /**
   * The minimum string length to generate, inclusive.
   */
  private final int my_min_length;
  
  /**
   * The maximum string length to generate, exclusive.
   */
  private final int my_max_length;

  /**
   * The minimum character to generate, inclusive.
   */
  private final int my_min_char;
  
  /**
   * The maximum character to generate, exclusive.
   */
  private final int my_max_char;
  
  /**
   * Constructs a new RandomString to generate random 7-bit printable 
   * strings (ASCII 32 to ASCII 126) with lengths between the given minimum 
   * value (inclusive) and maximum value (exclusive).
   * 
   * @param the_min_length The minimum string length to generate (inclusive).
   * @param the_max_length The maximum string length to generate (exclusive).
   * @exception IllegalArgumentException if the maximum length is less
   * than or equal to the minimum length, the maximum character is less
   * than the minimum character, or the minimum length is less
   * than 0.
   */
  public RandomString(final int the_min_length, final int the_max_length) 
    throws IllegalArgumentException {
    this(the_min_length, the_max_length, MIN_PRINTABLE, MAX_PRINTABLE);
  }

  /**
   * Constructs a new RandomString to generate random strings with 
   * lengths between the given minimum value (inclusive) and maximum 
   * value (exclusive), and characters between the given minimum 
   * character and maximum character (both inclusive).
   * 
   * @param the_min_length The minimum string length to generate (inclusive).
   * @param the_max_length The maximum string length to generate (exclusive).
   * @param the_min_char The minimum char value to place in the string
   * (inclusive).
   * @param the_max_char The maximum char value to place in the string
   * (inclusive).
   * @exception IllegalArgumentException if the maximum length is less
   * than or equal to the minimum length, the maximum character is less
   * than the minimum character, or the minimum length is less
   * than 0.
   */
  public RandomString(final int the_min_length, final int the_max_length,
                      final char the_min_char, final char the_max_char) 
    throws IllegalArgumentException {
    this(the_min_length, the_max_length, the_min_char, the_max_char, 
         Double.doubleToLongBits(Math.random()));
  }
  
  /**
   * Constructs a new RandomString to generate random strings with 
   * lengths between the given minimum value (inclusive) and maximum 
   * value (exclusive), and characters between the given minimum 
   * character and maximum character (both inclusive), using the 
   * specified random seed.
   * 
   * @param the_min_length The minimum string length to generate (inclusive).
   * @param the_max_length The maximum string length to generate (exclusive).
   * @param the_min_char The minimum char value to place in the string
   * (inclusive).
   * @param the_max_char The maximum char value to place in the string
   * (inclusive).
   * @param the_seed The random seed.
   * @exception IllegalArgumentException if the maximum length is less
   * than or equal to the minimum length, the maximum character is less
   * than the minimum character, or the minimum length is less
   * than 0.
   */
  public RandomString(final int the_min_length, final int the_max_length,
                      final char the_min_char, final char the_max_char,
                      final long the_seed) 
    throws IllegalArgumentException {
    if (the_max_length <= the_min_length) {
      throw new IllegalArgumentException(the_max_length + " <= " + the_min_length);
    } else if (the_max_char < the_min_char) {
      throw new IllegalArgumentException(the_min_char + " < " + the_max_char);
    } else if (the_min_length < 0) {
      throw new IllegalArgumentException(the_min_length + " < 0");
    }
    my_random = new Random(the_seed);
    my_min_length = the_min_length;
    my_max_length = the_max_length;
    my_min_char = the_min_char;
    my_max_char = the_max_char + 1;
  }
  
  @Override
  public String generate() {
    final int length = my_random.nextInt(my_max_length - my_min_length) + my_min_length;
    final StringBuilder result = new StringBuilder(length);
    for (int i = 0; i < length; i++) {
      result.append((char) (my_random.nextInt(my_max_char - my_min_char) + my_min_char));
    }
    return result.toString();
  }

  @Override
  public Class<?> generatedClass() {
    return String.class;
  }
}

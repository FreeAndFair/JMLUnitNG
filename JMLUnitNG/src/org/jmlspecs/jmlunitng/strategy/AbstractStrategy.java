/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.strategy;

/**
 * The parent of all strategy classes, contains bookkeeping information
 * for random data sampling.
 * 
 * @author Daniel M. Zimmerman
 * @version February 2011
 */
public abstract class AbstractStrategy implements Strategy {
  /**
   * The fraction of data values to include in the iterator,
   * 1 by default.
   */
  private double my_fraction = 1.0;
  
  /**
   * The random seed to use for sampling data values, 0 by default.
   */
  private long my_seed;
    
  /**
   * Sets the fraction of strategy values to include in the iterator.
   * Values greater than or equal to 1 include all the strategy values,
   * and values less than 0 include only the first strategy value.
   * 
   * @param the_fraction The fraction of values to include. 
   */
  public final void setFraction(final double the_fraction) {
    my_fraction = the_fraction;
  }
  
  /**
   * @return the fraction of strategy values to include in the iterator.
   */
  public final double fraction() {
    return my_fraction;
  }
  
  /**
   * Sets the random seed to be used when sampling values for the iterator.
   * 
   * @param the_seed The random seed.
   */
  public final void setSeed(final long the_seed) {
    my_seed = the_seed;
  }
  
  /**
   * @return the random seed to be used when sampling values for the iterator.
   */
  public final long seed() {
    return my_seed;
  }
}

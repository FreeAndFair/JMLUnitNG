/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng;

/**
 * An error class thrown by JMLUnitNG when things go irrecoverably wrong.
 * This is used instead of System.exit(), to allow JMLUnitNG to be used
 * as a module by other software (it is far easier to catch a
 * JMLUnitNGError than to catch an exit of the runtime).
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public class JMLUnitNGError extends Error {
  /**
   * Construct a new JMLUnitNGError with the specified detail message.
   * 
   * @param the_message The detail message.
   */
  public JMLUnitNGError(final String the_message) {
    super(the_message);
  }
  
  /**
   * Construct a new JMLUnitNGError with the specified Throwable cause.
   * 
   * @param the_cause The Throwable that caused this error. 
   */
  public JMLUnitNGError(final Throwable the_cause) {
    super(the_cause);
  }
}

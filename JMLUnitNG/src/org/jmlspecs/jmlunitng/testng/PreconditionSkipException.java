/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.testng;

import org.testng.SkipException;

/**
 * A SkipException for precondition violations.
 * 
 * @author Daniel M. Zimmerman
 * @version 1.0
 */

public class PreconditionSkipException extends SkipException {
  /**
   * 
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructs the PreconditionSkipException Object.
   * 
   * @param the_skip_message String != null
   */
  public PreconditionSkipException(final String the_skip_message) {
    super(the_skip_message);
  }

}

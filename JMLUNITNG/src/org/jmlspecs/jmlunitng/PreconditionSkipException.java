
package org.jmlspecs.jmlunitng;

import org.testng.SkipException;

/**
 * An Exception for precondition violation.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */

public class PreconditionSkipException extends SkipException
{

  /**
   * 
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructs the PreconditionSkipException Object.
   * 
   * @param the_skip_message String != null
   */
  public PreconditionSkipException(final String the_skip_message)
  {
    super(the_skip_message);
  }

}

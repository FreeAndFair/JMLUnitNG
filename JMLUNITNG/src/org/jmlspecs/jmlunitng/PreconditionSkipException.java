
package org.jmlspecs.jmlunitng;

import org.testng.SkipException;

/**
 * An Exception for precondition violation.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */

public class PreconditionSkipException extends SkipException
{

/**Constructs the PreconditionSkipException Object.
 * @param the_skipMessage String != null
 */
  public PreconditionSkipException(final String the_skipMessage)
  {
    super(the_skipMessage);
  }

}

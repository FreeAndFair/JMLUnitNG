/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.testng;

import org.testng.SkipException;

/**
 * A SkipException for precondition violations.
 * 
 * @author Daniel M. Zimmerman
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

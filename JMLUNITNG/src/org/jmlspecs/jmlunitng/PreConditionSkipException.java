
package org.jmlspecs.jmlunitng;

import org.testng.SkipException;

/**
 * An Exception for precondition violation.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */

public class PreConditionSkipException extends SkipException {

/**Constructs the PreconditionSkipException Object.
 * @param skipMessage String != null
 */
public PreConditionSkipException(String skipMessage) {
	super(skipMessage);

	}

}

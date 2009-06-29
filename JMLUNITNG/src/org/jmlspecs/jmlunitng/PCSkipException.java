
package org.jmlspecs.jmlunitng;

import org.testng.SkipException;

/**
 * An Exception for precondition violation.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */

public class PCSkipException extends SkipException {

/**Constructs the PreconditionSkipException Object.
 * @param skipMessage String != null
 */
public PCSkipException(String skipMessage) {
	super(skipMessage);

	}

}

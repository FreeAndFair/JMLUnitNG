package org.jmlspecs.jmlunitng;

import org.testng.SkipException;
/**
 * An Exception for precondition violation
 *
 * @author Rinkesh Nagmoti
 * @version 
 */

public class PreConditionSkipException extends SkipException {

	
	public PreConditionSkipException(String skipMessage) {
		super(skipMessage);
		
	}

}

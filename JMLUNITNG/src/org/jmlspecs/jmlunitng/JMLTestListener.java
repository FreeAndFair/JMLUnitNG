package org.jmlspecs.jmlunitng;

import junit.framework.TestListener;
import junit.framework.Test;

/**
 * A listener for test progress that takes into account meaningless
 * test results (in which an entry precondition was false).
 *
 * @author Rinkesh Nagmoti
 * @version $Revision: 1.2 $
 */
public interface JMLTestListener extends TestListener {
    
    /**
     * A meaningless test (in which an entry precondition was false)
     * was executed.
     */
    void addMeaningless(Test test);
}

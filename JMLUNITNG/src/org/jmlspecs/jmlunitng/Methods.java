package org.jmlspecs.jmlunitng;

import java.util.List;

/**
 * Class containing the arraylist of methods to be tested.
 * @author Rinkesh Nagmoti
 *@version 1.0
 */
public class Methods {

	/** Constructs the Methods Object.*/
    public Methods(List methods, List inheritedMethods) {
    	this.methods = methods;
    	this.inheritedMethods = inheritedMethods;
    }

    /** Returns the combined list of methods to be tested.*/
    public List getCombinedMethodsList() {
    	List tempList = null;
    	tempList.addAll(methods);
    	tempList.addAll(inheritedMethods);

    	return tempList;
    }
    //----------------
    //DATA MEMBERS
    //----------------
    /** List of all methods to be tested.*/
    protected List methods;
    /** List of all inherted methods to be tested.*/
    protected List inheritedMethods;
}

package org.jmlspecs.jmlunitng;

import org.multijava.mjc.CMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;

/**
 * Represents method information for the method to be tested.  
 * @author Rinkesh Nagmoti 
 * @version 1.0
 */
public class MethodToBeTested {
	
	/** Constructs the Object to of MethodToBeTested.*/
	public MethodToBeTested(CMethod method) { 
		returnType = method.returnType();
		modifier = method.modifiers();
		methodName= method.getIdent();
		CSpecializedType[] ts = method.parameters();
        parameters = new Parameter[ts.length];
         for (int i = 0; i < ts.length; i++) {
             parameters[i] = new Parameter(ts[i].staticType(),
                                       "arg" + (i+1));
         }
	}
    
	/** Returns the return type of the method.*/
	public CType getReturnType() {
		return returnType;
	}
	/** Returns the modifier for the method.*/
	public long getModifier() {
		return modifier;
	}
	/** Return the name of the method.*/
	public String getName() {
		return methodName;
	}
	public Parameter[] getParaters() {
		return parameters;
	}
	//-------------
	//DATA MEMBERS
	//-------------
   /** Represents the return type of the method.*/
    private CType returnType;
   /** Represents the method's modifiers.*/
    private long modifier;
   /** Represents the name of the Method.*/
    private String methodName;
   /** The method's parameters */
    private Parameter[] parameters;
}

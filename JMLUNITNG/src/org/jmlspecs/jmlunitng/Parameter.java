package org.jmlspecs.jmlunitng;

import org.multijava.mjc.CType;

public class Parameter {
    Parameter(CType type, String ident) {
        this.ctype = type;
        this.type = type.toString();
        this.ident = ident;
    }

    /** The ctype of this parameter */
    protected CType ctype;
    /** The string name of this type */
    protected String type;
    /** The variable's name */
    protected String ident;
}
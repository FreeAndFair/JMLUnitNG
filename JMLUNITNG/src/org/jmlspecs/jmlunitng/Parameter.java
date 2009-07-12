
package org.jmlspecs.jmlunitng;

import org.multijava.mjc.CType;

/**
 * Stores the information about the parameter.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 * 
 */
public class Parameter
{
  /** The CType of this parameter. */
  final CType my_ctype;
  /** The string name of this type. */
  final String my_type;
  /** The variable's name. */
  final String my_ident;

  /**
   * Constructs the parameter object.
   * 
   * @param the_type
   * @param the_ident
   */
  public Parameter(final CType the_type, final String the_ident)
  {
    this.my_ctype = the_type;
    this.my_type = the_type.toString();
    this.my_ident = the_ident;
  }

}

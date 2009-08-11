
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
  private final transient CType my_ctype;
  /** The string name of this type. */
  private final transient String my_type;
  /** The variable's name. */
  private final transient String my_ident;

  /**
   * Constructs the parameter object.
   * 
   * @param the_type The CType object.
   * @param the_ident The String for identity.
   */
  public Parameter(final CType the_type, final String the_ident)
  {
    this.my_ctype = the_type;
    this.my_type = the_type.toString();
    this.my_ident = the_ident;
  }
 /**
  *  This is the CType. 
  * @return CType
  */
  public CType getCType()
  {
    return my_ctype;
  }
/**
 *  This is the String type.
 * @return String
 */
  public String getType()
  {
    return my_type;
  }
  /**
   * This is the identity. 
   * @return String.
   */
  public String getident()
  {
    return my_ident;
  }
}

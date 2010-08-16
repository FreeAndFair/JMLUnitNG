/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "May 2010"
 * @last_updated_date "May 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.generator;

/**
 * Information about a method parameter.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version August 2010
 */
public class ParameterInfo {
  /**
   * The parameter type.
   */
  private final /*@ non_null @*/ TypeInfo my_type;
  
  /**
   * The parameter name.
   */
  private final /*@ non_null @*/ String my_name;
  
  /**
   * Is this parameter an array?
   */
  private final boolean my_is_array;
  
  /**
   * Create a new ParameterInfo with the given fully qualified name and parameter name.
   * 
   * @param the_type The fully qualified name of the type.
   * @param the_name The name of the parameter.
   * @param the_is_array true if the parameter type is an array type, false otherwise.
   */
  public ParameterInfo(final /*@ non_null @*/ String the_type, 
                       final /*@ non_null @*/ String the_name, 
                       final boolean the_is_array) {
    my_type = new TypeInfo(the_type);
    my_name = the_name;
    my_is_array = the_is_array;
  }
  
  /**
   * @return The parameter type.
   */
  public final TypeInfo type() {
    return my_type;
  }
  
  /**
   * @return The parameter name.
   */
  public final String name() {
    return my_name;
  }
  
  /**
   * @return True if this parameter is an array. False otherwise.
   */
  public final boolean isArray() {
    return my_is_array;
  }

}

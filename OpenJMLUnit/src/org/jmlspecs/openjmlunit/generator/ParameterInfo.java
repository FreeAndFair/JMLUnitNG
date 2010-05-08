/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "May 2010"
 * @last_updated_date "May 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

/**
 * Name information about a method parameter.
 * 
 * @author Jonathan Hogins
 * @version May 2010
 */
public class ParameterInfo extends TypeInfo {
  /**
   * The parameter name.
   */
  private final String my_param_name;
  
  /**
   * Create a new ParameterInfo with the given fully qualified name and parameter name.
   * @param the_type The fully qualified name of the type.
   * @param the_parameter_name The name of the parameter.
   */
  public ParameterInfo(final String the_type, final String the_parameter_name) {
    super(the_type);
    my_param_name = the_parameter_name;
  }
  
  /**
   * Returns the parameter name.
   * @return The parameter name.
   */
  public final String getParameterName() {
    return my_param_name;
  }
}

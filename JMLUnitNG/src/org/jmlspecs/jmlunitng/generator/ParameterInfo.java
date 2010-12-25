/*
 * JMLUnitNG 
 * Copyright (C) 2010
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
  public final TypeInfo getType() {
    return my_type;
  }
  
  /**
   * @return The parameter name.
   */
  public final String getName() {
    return my_name;
  }
  
  /**
   * @return True if this parameter is an array. False otherwise.
   */
  public final boolean isArray() {
    return my_is_array;
  }

  /**
   * {@inheritDoc}
   */
  public boolean equals(final /*@ nullable @*/ Object the_other) {
    boolean result = false;
    
    if (the_other != this && the_other != null && the_other.getClass() == getClass()) {
      final ParameterInfo param = (ParameterInfo) the_other;
      result = my_type.equals(param.my_type);
      result &= my_name.equals(param.my_name);
      result &= my_is_array == param.my_is_array;
    }
    
    return result;
  }
  
  /**
   * {@inheritDoc}
   */
  public int hashCode() {
    return my_type.hashCode() + my_name.hashCode();
  }
}

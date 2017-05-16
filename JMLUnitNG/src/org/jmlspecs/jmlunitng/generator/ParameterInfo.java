/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.generator;

/**
 * Information about a method parameter.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version January 2011
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
   * Create a new ParameterInfo with the given fully qualified name and parameter name.
   * 
   * @param the_type The fully qualified name of the type.
   * @param the_name The name of the parameter.
   */
  public ParameterInfo(final /*@ non_null @*/ String the_type, 
                       final /*@ non_null @*/ String the_name) {
    my_type = new TypeInfo(the_type);
    my_name = the_name;
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
   * {@inheritDoc}
   */
  public boolean equals(final /*@ nullable @*/ Object the_other) {
    boolean result = false;
    
    if (the_other != this && the_other != null && the_other.getClass() == getClass()) {
      final ParameterInfo param = (ParameterInfo) the_other;
      result = my_type.equals(param.my_type);
      result &= my_name.equals(param.my_name);
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

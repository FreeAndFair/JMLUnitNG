/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.generator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Name information about a type.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version August 2010
 */
public class TypeInfo {
  /**
   * The set of primitive types.
   */
  private static final Set<String> PRIMITIVE_TYPES;

  static {
    final Set<String> prims = new HashSet<String>();
    prims.add("boolean");
    prims.add("int");
    prims.add("long");
    prims.add("float");
    prims.add("double");
    prims.add("byte");
    prims.add("short");
    prims.add("char");
    prims.add("java.lang.String");
    PRIMITIVE_TYPES = Collections.unmodifiableSet(prims);
  }

  /**
   * The fully qualified name of the class.
   */
  protected final String my_name;

  /**
   * The unqualified name of the class.
   */
  protected final String my_short_name;

  /**
   * The generic component of the class.
   */
  protected final String my_generic_comp;

  /**
   * The array dimension of the class.
   */
  protected final int my_array_dimension;
    
  /**
   * Create a new Type with the given fully qualified name. 
   * If the given fully qualified name has a generic portion, it is removed.
   * 
   * @param the_name The fully qualified name of the type.
   */
  // @ ensures my_generic_comp != null <==> the_name.indexOf('<') != the_name.length;
  public TypeInfo(final String the_name) {
    int generic_start = the_name.indexOf('<');
    int generic_end = the_name.indexOf('[');
    String array_part = "";
    if (generic_end == -1) {
      generic_end = the_name.length();
    } else {
      array_part = the_name.substring(generic_end, the_name.length());
    }
    if (generic_start == -1) {
      generic_start = Math.min(generic_end, the_name.length());
      my_generic_comp = "";
    } else {
      my_generic_comp = the_name.substring(generic_start, generic_end);
    }
    my_name = the_name.substring(0, generic_start) + array_part;
    my_short_name = my_name.substring(my_name.lastIndexOf('.') + 1);
    my_array_dimension = array_part.length() / 2;
  }

  /**
   * @return The unqualified name of the class.
   */
  public String getShortName() {
    return my_short_name;
  }

  /**
   * @return The fully qualified name of the class, without generic information.
   */
  public String getFullyQualifiedName() {
    return my_name;
  }
  
  /**
   * @return The generic component of the type.
   */
  public String getGenericComponent() {
    return my_generic_comp;
  }

  /**
   * @return A formatted fully qualified name of the type, with '.' characters
   * replaced by '_' and array brackets replaced with a notation of the array
   * dimension.
   */
  public String getFormattedName() {
    final StringBuilder formatted = new StringBuilder(my_name.replace('.', '_'));
   
    if (isArray()) {
      formatted.delete(formatted.indexOf("[]"), formatted.length());
      formatted.append(arrayDimension() + "DArray");
    }
    
    return formatted.toString();
  }

  /**
   * @return true if this class is in a package, false otherwise.
   */
  public boolean isPackaged() {
    return my_name.length() > my_short_name.length();
  }
  
  /**
   * @return The package name of the class
   */
  public String getPackageName() {
    String result = "";

    if (my_name.length() > my_short_name.length()) {
      result = my_name.substring(0, my_name.length() - my_short_name.length() - 1);
    }

    return result;
  }

  /**
   * @return true if the type is a primitive, false otherwise.
   */
  // @ensures \result == PRIMITIVE_TYPES.contains(my_name);
  public boolean isPrimitive() {
    return PRIMITIVE_TYPES.contains(my_name);
  }

  /**
   * @return true if the type is an array type, false otherwise.
   */
  //@ ensures \result == arrayDimension() > 0;
  public boolean isArray() {
    return my_array_dimension > 0;
  }
  
  /**
   * @return the array dimension, 0 if not an array.
   */
  //@ ensures \result >= 0;
  public int arrayDimension() {
    return my_array_dimension;
  }
  
  /**
   * Compares with object for equality. Two ClassInfo objects are equal if they
   * have the same fully qualified name.
   * 
   * @param the_other The object to compare.
   * @return true if qualified names are equal. false otherwise.
   */
  public boolean equals(final /*@ nullable @*/ Object the_other) {
    boolean result = false;
    
    if (the_other != this && the_other != null && the_other.getClass() == getClass()) {
      final TypeInfo type = (TypeInfo) the_other;
      result = my_name.equals(type.my_name);
      result &= my_short_name.equals(type.my_short_name);
      result &= my_generic_comp.equals(type.my_generic_comp);
    } else if (the_other == this) {
      result = true;
    }

    return result;
  }

  /**
   * @return A hash code for this object.
   */
  public int hashCode() {
    return my_name.hashCode();
  }

  /**
   * @return The fully qualified name.
   */
  public String toString() {
    return getFullyQualifiedName();
  }
}

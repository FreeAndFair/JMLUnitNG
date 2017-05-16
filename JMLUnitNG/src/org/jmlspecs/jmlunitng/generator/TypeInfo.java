/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
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
 * @version January 2011
 */
public class TypeInfo implements Comparable<TypeInfo> {
  /**
   * The set of primitive types.
   */
  private static final Set<String> PRIMITIVE_TYPES;

  static {
    final Set<String> prims = new HashSet<String>();
    prims.add("boolean");
    prims.add("java.lang.Boolean");
    prims.add("int");
    prims.add("java.lang.Integer");
    prims.add("long");
    prims.add("java.lang.Long");
    prims.add("float");
    prims.add("java.lang.Float");
    prims.add("double");
    prims.add("java.lang.Double");
    prims.add("byte");
    prims.add("java.lang.Byte");
    prims.add("short");
    prims.add("java.lang.Short");
    prims.add("char");
    prims.add("java.lang.Character");
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
   * The formatted name of this class.
   */
  protected final String my_formatted_name;
  
  /**
   * The formatted short name of this class.
   */
  protected final String my_formatted_short_name;
  
  /**
   * The generic component of the class.
   */
  protected final String my_generic_comp;

  /**
   * The array dimension of the class.
   */
  protected final int my_array_dimension;
    
  /**
   * The array component of the class.
   */
  protected final String my_array_comp;
  
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
    if (isArray()) {
      my_array_comp = my_name.substring(0, my_name.lastIndexOf('['));
    } else {
      my_array_comp = null;
    }
    my_formatted_name = formatName(my_name);
    my_formatted_short_name = formatName(my_short_name);
  }

  /**
   * @param the_name The name of a class.
   * @return the formatted name corresponding to the specified class name; 
   * this replaces all "." with "_" and changes array delimiters to "nDArray".
   */
  private String formatName(final String the_name) {
    final StringBuilder formatted = new StringBuilder(the_name.replace('.', '_'));
    if (isArray()) {
      formatted.delete(formatted.indexOf("[]"), formatted.length());
      formatted.append(my_array_dimension + "DArray");
    } 
    return formatted.toString();
  }
  
  /**
   * @return The unqualified name of the class.
   */
  public final String getShortName() {
    return my_short_name;
  }

  /**
   * @return The fully qualified name of the class, without generic information.
   */
  public final String getFullyQualifiedName() {
    return my_name;
  }
  
  /**
   * @return The generic component of the type.
   */
  public final String getGenericComponent() {
    return my_generic_comp;
  }

  /**
   * @return A formatted fully qualified name of the type, with '.' characters
   * replaced by '_' and array brackets replaced with a notation of the array
   * dimension.
   */
  public final String getFormattedName() {
    return my_formatted_name;
  }

  /**
   * @return A formatted short name of the type, with array brackets replaced with
   * a notation of the array dimension.
   */
  public final String getFormattedShortName() {
    return my_formatted_short_name;
  }
  
  /**
   * @return true if this class is in a package, false otherwise.
   */
  public final boolean isPackaged() {
    return my_name.length() > my_short_name.length();
  }
  
  /**
   * @return The package name of the class
   */
  public final String getPackageName() {
    String result = "";

    if (my_name.length() > my_short_name.length()) {
      result = my_name.substring(0, my_name.length() - my_short_name.length() - 1);
    }

    return result;
  }

  /**
   * @return true if the type is treated as a primitive, false otherwise.
   */
  // @ensures \result == PRIMITIVE_TYPES.contains(my_name);
  public final boolean isPrimitive() {
    return PRIMITIVE_TYPES.contains(my_name);
  }

  /**
   * @return true if the type is an array type, false otherwise.
   */
  //@ ensures \result == arrayDimension() > 0;
  public final boolean isArray() {
    return my_array_dimension > 0;
  }
  
  /**
   * @return the array dimension, 0 if not an array.
   */
  //@ ensures \result >= 0;
  public final int arrayDimension() {
    return my_array_dimension;
  }
  
  /**
   * @return the array component type, or null if not an array.
   */
  public final String getArrayComponent() {
    return my_array_comp;
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
  
  /**
   * Compares this TypeInfo to the_other; TypeInfos are compared based on their
   * fully qualified names.
   * 
   * @param the_other The other ClassInfo.
   * @return -1, 0 or 1 as this ClassInfo is less than, equivalent to, or greater 
   * than the_other respectively.
   */
  public int compareTo(final TypeInfo the_other) {
    return getFullyQualifiedName().compareTo(the_other.getFullyQualifiedName());
  }
}

/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "May 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Name information about a type.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public class TypeInfo {
  /**
   * The set of primitive types.
   */
  private static final Set<String> PRIMITIVE_TYPES;

  static {
    Set<String> prims = new HashSet<String>();
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
   * The fully qualified name of this class.
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

  // @ invariant my_short_name.equals(my_name.substring(my_name.lastIndexOf('.') + 1));
  /**
   * Create a new Type with the given fully qualified name. If the given fully qualified name has a generic portion, it is removed.
   * 
   * @param the_name The fully qualified name of the type.
   */
  // @ ensures my_generic_comp != null <==> the_name.indexOf('<') != the_name.length;
  public TypeInfo(final String the_name) {
    int generic_start = the_name.indexOf('<');
    if (generic_start == -1) {
      generic_start = the_name.length();
      my_generic_comp = "";
    } else {
      my_generic_comp = the_name.substring(generic_start, the_name.length() - 1);
    }
    my_name = the_name.substring(0, generic_start);
    my_short_name = the_name.substring(my_name.lastIndexOf('.') + 1);
  }

  /**
   * Returns the unqualified name of the class.
   * 
   * @return The name of the class
   */
  public String getShortName() {
    return my_short_name;
  }

  /**
   * Returns the fully qualified name of the class. Does not include generics information.
   * 
   * @return The name of the class
   */
  public String getFullyQualifiedName() {
    return my_name;
  }
  
  /**
   * Returns the generic component of the type or the empty string if one does not exist.
   * 
   * @return The generic component of the type.
   */
  public String getGenericComponent() {
    return my_generic_comp;
  }

  /**
   * Returns the fully qualified name of the type with '.' characters replaced
   * by '_' and [] replaced with "Array".
   * 
   * @return Formatted fully qualified name of the type.
   */
  public String getFormattedName() {
    return my_name.replace('.', '_').replaceAll("\\[\\]", "Array");
  }

  /**
   * Returns the package name of the class.
   * 
   * @return The package name of the class
   */
  public String getPackageName() {
    if (my_name.length() > my_short_name.length()) {
      return my_name.substring(0, my_name.length() - my_short_name.length() - 1);
    } else {
      return "";
    }
  }

  /**
   * Returns true if the type is a primitive, false otherwise. Primitive types
   * are "boolean", "int", "long", "float", "double", "byte", "short", "char",
   * and "java.lang.String".
   * 
   * @return true if the type is a primitive, false otherwise.
   */
  // @ensures \result == PRIMITIVE_TYPES.contains(my_name);
  public boolean isPrimitive() {
    return PRIMITIVE_TYPES.contains(my_name);
  }

  /**
   * Compares with object for equality. To ClassInfo objects are equal if they
   * have the same fully qualified names.
   * 
   * @param the_o The object to compare.
   * @return true if qualified names are equal. false otherwise.
   */
  public boolean equals(final Object the_o) {
    if (the_o != null && the_o instanceof TypeInfo) {
      return ((TypeInfo) the_o).my_name.equals(my_name);
    } else {
      return false;
    }
  }

  /**
   * Returns a hash of this object.
   * 
   * @return The hash code of this object.
   */
  public int hashCode() {
    return my_name.hashCode();
  }

  /**
   * Returns the fully qualified name as the string representation of the type.
   * 
   * @return The fully qualified name.
   */
  public String toString() {
    return getFullyQualifiedName();
  }
}

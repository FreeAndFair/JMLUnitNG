/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "April 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.generator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * Information about a method under test.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public class MethodInfo {
  /**
   * The static set of untestable method names.
   */
  private static final Set<String> UNTESTABLE_METHOD_NAMES;
  static {
    final Set<String> untestable_methods = new HashSet<String>();
    untestable_methods.add("finalize");
    untestable_methods.add("getClass");
    untestable_methods.add("notify");
    untestable_methods.add("notifyAll");
    untestable_methods.add("wait");
    UNTESTABLE_METHOD_NAMES = Collections.unmodifiableSet(untestable_methods);
  }
  /**
   * The name of the method.
   */
  private String my_name;
  /**
   * The protection level of the method.
   */
  private ProtectionLevel my_protection_level;

  /**
   * The name of the return type of the method.
   */
  private TypeInfo my_return_type;

  /**
   * The parameter types of the method in order.
   */
  private List<ParameterInfo> my_parameter_types;

  /**
   * The ClassInfo for the class this method belongs to.
   */
  private ClassInfo my_parent_class;

  /**
   * The ClassInfo for the class this method is declared in.
   */
  private ClassInfo my_declaring_class;

  /**
   * Is the method static?
   */
  private boolean my_is_static;

  /**
   * Is the method a constructor?
   */
  private boolean my_is_constructor;

  /*@ invariant my_is_inherited == !my_declaring_class.equals(my_parent_class); */
  /**
   * Is the method inherited?
   */
  private boolean my_is_inherited;
  
  /**
   * Is the method a factory?
   */
  private boolean my_is_factory;

  /*@ invariant my_is_testable == 
    @        !(my_is_constructor && my_parent_class.isAbstract()) &&
    @        !my_protection_level.equals(ProtectionLevel.PRIVATE) && 
    @            !UNTESTABLE_METHOD_NAMES.contains(my_name); */
  /**
   * Is the method testable?
   */
  private boolean my_is_testable;

  /**
   * Creates a MethodInfo object representing a method with the given
   * parameters.
   * 
   * @param the_name The name of the method.
   * @param the_parent_class The ClassInfo for the class this method belongs to.
   * @param the_declaring_class The ClassInfo for the class this method is
   *          declared in.
   * @param the_protection_level The protection level of the method.
   * @param the_parameter_types The parameter types of the method in order.
   * @param the_return_type The name of the return type of the method.
   * @param the_is_constructor Is the method a constructor?
   * @param the_is_static Is the method static?
   */
  //@ requires !the_is_constructor || !the_is_static;
  public MethodInfo(final String the_name, final ClassInfo the_parent_class,
                    final ClassInfo the_declaring_class,
                    final ProtectionLevel the_protection_level,
                    final List<ParameterInfo> the_parameter_types, final TypeInfo the_return_type,
                    final boolean the_is_constructor, final boolean the_is_static) {
    my_name = the_name;
    my_parent_class = the_parent_class;
    my_declaring_class = the_declaring_class;
    my_protection_level = the_protection_level;
    my_parameter_types = Collections.unmodifiableList(the_parameter_types);
    my_return_type = the_return_type;
    my_is_static = the_is_static;
    my_is_constructor = the_is_constructor;

    my_is_inherited = !the_parent_class.equals(the_declaring_class);
    my_is_factory = determineIsFactory();
    my_is_testable =
        !(my_is_constructor && my_declaring_class.isAbstract()) &&
        !my_protection_level.equals(ProtectionLevel.PRIVATE) &&
        !UNTESTABLE_METHOD_NAMES.contains(my_name);
  }

  /**
   * Returns the name of the method.
   * 
   * @return The name of the method
   */
  public/*@pure*/String getName() {
    return my_name;
  }

  /**
   * Returns the ClassInfo object for the class who owns this method.
   * 
   * @return The ClassInfo object for the class who owns this method.
   */
  public/*@ pure */ClassInfo getParentClass() {
    return my_parent_class;
  }

  /**
   * Returns the ClassInfo object for the class who declared this method.
   * 
   * @return The ClassInfo object for the class who declared this method.
   */
  public/*@ pure */ClassInfo getDeclaringClass() {
    return my_declaring_class;
  }

  /**
   * Returns the protection level of the method.
   * 
   * @return The protection level of the method.
   */
  public/*@pure */ProtectionLevel getProtectionLevel() {
    return my_protection_level;
  }

  /**
   * Returns an unmodifiable list of the parameter types for this method in
   * order.
   * 
   * @return A list of parameter types.
   */
  public/*@pure */List<ParameterInfo> getParameterTypes() {
    return my_parameter_types;
  }

  /**
   * Returns the return type of this method as a String.
   * 
   * @return The return type.
   */
  public/*@ pure */TypeInfo getReturnType() {
    return my_return_type;
  }

  // "Is the method a constructor?",
  /**
   * Returns true if this method is a constructor. False if not.
   * 
   * @return True if this method is a constructor. False if not.
   */
  public/*@ pure */boolean isConstructor() {
    return my_is_constructor;
  }

  // "Is the method a factory?",
  /**
   * Returns true if this method is a factory method. A factory method is
   * defined as a static method whose return type is the same as the class it
   * belongs to or an abstract parent class thereof.
   * 
   * @return True if this method is a factory. False otherwise.
   * 
   */
  public/*@ pure */boolean isFactory() {
    return my_is_factory;
  }

  // "Is the method static?",
  /**
   * Returns true if this method is a static method. False if not.
   * 
   * @return True if this method is static. False if not.
   */
  public/*@ pure */boolean isStatic() {
    return my_is_static;
  }

  // "Is the method testable?",
  /**
   * Returns whether or not this method is testable. A method is testable if and
   * only if it a) is not a constructor of an abstract class, 
   * b)has a non-private protection level, and c) is not (and does not
   * override) one of the following methods from java.lang.Object: finalize,
   * getClass, notify, notifyAll, wait.
   * 
   * @return True if this method is testable. False otherwise.
   */
  public/*@ pure */boolean isTestable() {
    return my_is_testable;
  }

  // "Is the method inherited?"

  /**
   * Returns true if this method was inherited. False otherwise.
   * 
   * @return True if this method was inherited. False otherwise.
   */
  public/*@ pure */boolean isInherited() {
    return my_is_inherited;
  }
  
  /**
   * Determines whether or not this method is a factory method.
   * @return True if this method is a factory. False otherwise.
   */
  private /*@ pure */ boolean determineIsFactory() {
    //decide if factory
    ClassInfo cur = my_declaring_class;
    while (cur != null && my_name.equals(cur.getShortName())) {
      cur = cur.getSuperclassInfo();
    }
    return my_is_static && cur != null;
  }
  
  /**
   * Returns the signature of this method as a String.
   * @return The method signature
   */
  public /*@ pure */ String toString() {
    StringBuilder sb = new StringBuilder();
    if (my_return_type != null) {
      sb.append(my_return_type.getFullyQualifiedName());
      sb.append(" ");
    }
    sb.append(my_name);
    sb.append("(");
    Iterator<ParameterInfo> paramIter = my_parameter_types.iterator();
    while (paramIter.hasNext()) {
      ParameterInfo param = paramIter.next();
      sb.append(param.getFullyQualifiedName());
      sb.append(" ");
      sb.append(param.getParameterName());
      if (param.isArray()) {
        sb.append("[]");
      }
      if (paramIter.hasNext()) {
        sb.append(", ");
      }
    }
    sb.append(")");
    return sb.toString();
  }

}

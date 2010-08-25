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
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version August 2010
 */
public class MethodInfo {
  /**
   * The static set of untestable method names.
   */
  private static final /*@ non_null @*/ Set<String> UNTESTABLE_METHOD_NAMES;
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
  private final /*@ non_null @*/ String my_name;
  
  /**
   * The protection level of the method.
   */
  private final /*@ non_null @*/ ProtectionLevel my_protection_level;

  /**
   * The name of the return type of the method.
   */
  private final /*@ non_null @*/ TypeInfo my_return_type;

  /**
   * The parameter types of the method in order.
   */
  private final /*@ non_null @*/ List<ParameterInfo> my_parameter_types;

  /**
   * The ClassInfo for the class this method belongs to.
   */
  private final /*@ non_null @*/ ClassInfo my_parent_class;

  /**
   * The ClassInfo for the class this method is declared in.
   */
  private final /*@ non_null @*/ ClassInfo my_declaring_class;

  /**
   * Is the method static?
   */
  private final boolean my_is_static;

  /**
   * Is the method a constructor?
   */
  private final boolean my_is_constructor;

  /*@ invariant my_is_inherited == !my_declaring_class.equals(my_parent_class); */
  /**
   * Is the method inherited?
   */
  private final boolean my_is_inherited;
  
  /**
   * Is the method a factory?
   */
  private final boolean my_is_factory;

  /*@ invariant my_is_testable == 
    @        !(my_is_constructor && my_parent_class.isAbstract()) &&
    @        !my_protection_level.equals(ProtectionLevel.PRIVATE) && 
    @            !UNTESTABLE_METHOD_NAMES.contains(my_name); */
  /**
   * Is the method testable?
   */
  private final boolean my_is_testable;

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
  public MethodInfo(final /*@ non_null @*/ String the_name, 
                    final /*@ non_null @*/ ClassInfo the_parent_class,
                    final /*@ non_null @*/ ClassInfo the_declaring_class,
                    final /*@ non_null @*/ ProtectionLevel the_protection_level,
                    final /*@ non_null @*/ List<ParameterInfo> the_parameter_types, 
                    final /*@ non_null @*/ TypeInfo the_return_type,
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
   * @return The name of the method
   */
  public /*@ pure non_null @*/ String getName() {
    return my_name;
  }

  /**
   * @return The ClassInfo object for the class that owns this method.
   */
  public /*@ pure non_null @*/ ClassInfo getParentClass() {
    return my_parent_class;
  }

  /**
   * @return The ClassInfo object for the class that declared this method.
   */
  public /*@ pure non_null @*/ ClassInfo getDeclaringClass() {
    return my_declaring_class;
  }

  /**
   * @return The protection level of the method.
   */
  public /*@ pure non_null @*/ ProtectionLevel getProtectionLevel() {
    return my_protection_level;
  }

  /**
   * @return an unmodifiable list of the parameter types of the method,
   *  in the order they are declared in the parameter list.
   */
  public /*@ pure non_null @*/ List<ParameterInfo> getParameterTypes() {
    return my_parameter_types;
  }

  /**
   * @return The return type of the method.
   */
  public /*@ pure @*/ TypeInfo getReturnType() {
    return my_return_type;
  }

  /**
   * @return True if this method is a constructor. False if not.
   */
  public /*@ pure @*/ boolean isConstructor() {
    return my_is_constructor;
  }

  /**
   * Returns true if this method is a factory method. A factory method is
   * defined as a static method whose return type is the same as the class it
   * belongs to or an abstract parent class thereof.
   * 
   * @return True if this method is a factory. False otherwise.
   * 
   */
  public /*@ pure @*/ boolean isFactory() {
    return my_is_factory;
  }

  /**
   * Returns true if this method is a static method. False if not.
   * 
   * @return True if this method is static. False if not.
   */
  public /*@ pure @*/ boolean isStatic() {
    return my_is_static;
  }

  /**
   * Returns whether or not this method is testable. A method is testable if and
   * only if it a) is not a constructor of an abstract class, 
   * b)has a non-private protection level, and c) is not (and does not
   * override) one of the following methods from java.lang.Object: finalize,
   * getClass, notify, notifyAll, wait.
   * 
   * @return True if this method is testable. False otherwise.
   */
  public /*@ pure @*/ boolean isTestable() {
    return my_is_testable;
  }

  /**
   * @return True if this method was inherited. False otherwise.
   */
  public /*@ pure @*/ boolean isInherited() {
    return my_is_inherited;
  }
  
  /**
   * Determines whether or not this method is a factory method.
   * @return True if this method is a factory. False otherwise.
   */
  private /*@ pure @*/ boolean determineIsFactory() {
    //decide if factory
    ClassInfo cur = my_declaring_class;
    while (cur != null && my_name.equals(cur.getShortName())) {
      cur = cur.getParent();
    }
    return my_is_static && cur != null;
  }
  
  /**
   * @return The method signature as a String.
   */
  public /*@ pure non_null @*/ String toString() {
    final StringBuilder sb = new StringBuilder();
    if (my_return_type != null) {
      sb.append(my_return_type.getFullyQualifiedName());
      sb.append(" ");
    }
    sb.append(my_name);
    sb.append("(");
    final Iterator<ParameterInfo> paramIter = my_parameter_types.iterator();
    while (paramIter.hasNext()) {
      final ParameterInfo param = paramIter.next();
      sb.append(param.getType().getFullyQualifiedName());
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
  
  /**
   * {@inheritDoc}
   */
  public /*@ pure @*/ int hashCode() {
    return toString().hashCode();
  }
}

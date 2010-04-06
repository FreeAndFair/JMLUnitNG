package org.jmlspecs.openjmlunit.generator;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class MethodInfo {
  /**
   * The static set of untestable method names.
   */
  private static final Set<String> UNTESTABLE_METHOD_NAMES;
  static {
    HashSet<String> untestable_methods = new HashSet<String>();
    untestable_methods.add("finalize");
    untestable_methods.add("getClass");
    untestable_methods.add("notify");
    untestable_methods.add("notifyAll");
    untestable_methods.add("wait");
    UNTESTABLE_METHOD_NAMES = Collections.unmodifiableSet(untestable_methods);
  }
  /**
   * The Method represented by this class.
   */
  private Method my_method;
  /**
   * Is this method inherited?
   */
  private boolean my_is_inherited;

  /* @ensures isInherited() &&
   *          getMethod() == the_method;
   */
  public MethodInfo(Method the_method) {
    my_method = the_method;
    my_is_inherited = true;
  }

  /**
   * Protected constructor for use by the ClassInfo object. Uses the_class to
   * determine the return value of isInherited.
   * 
   * @param the_method The method to be represented.
   * @param the_class The class that contains this method.
   */
  /* @ensures isInherited() == (the_method.getDeclaringClass() == the_class) &&
   *          getMethod() == the_method;
   */
  protected MethodInfo(Method the_method, Class<?> the_class) {
    my_method = the_method;
    my_is_inherited = the_method.getDeclaringClass() == the_class;
  }

  /**
   * Returns the Method represented by this MethodInfo object.
   * 
   * @return The method represented by this object.
   */
  public/*@ pure */Method getMethod() {
    return my_method;
  }

  // "Is the method a constructor?",
  // "Is the method a factory?",
  /**
   * Returns true if this method is a factory method. A factory method is
   * defined as a static method whose return type is the same as the class it
   * belongs to or an abstract parent class thereof.
   */
  /*@ ensures isStatic() &&
    @  getMethod().getClass().isAssignableFrom(my_method.getReturnType()
  */
  public/*@ pure */boolean isFactory() {
    return isStatic()
        && my_method.getClass().isAssignableFrom(my_method.getReturnType());
  }

  // "Is the method static?",
  /**
   * Returns true if this method is a factory method. A factory method is
   * defined as a static method whose return type is the same as the class it
   * belongs to or an abstract parent class thereof.
   */
  /*@ ensures getMethod().getModifiers() & Modifier.STATIC) > 0
  */
  public/*@ pure */boolean isStatic() {
    return (my_method.getModifiers() & Modifier.STATIC) > 0;
  }

  // "Is the method testable?",
  /**
   * Returns whether or not this method is testable. A method is testable if and
   * only if it has a non-private protection level and does not (and does not
   * override) one of the following methods from java.lang.Object: finalize,
   * getClass, notify, notifyAll, wait.
   * 
   * @return True if this method is testable. False otherwise.
   */
  public/*@ pure */boolean isTestable() {
    return !UNTESTABLE_METHOD_NAMES.contains(my_method.getName());
  }

  // "Is the method inherited?"

  /**
   * Returns true if this method was inherited. False otherwise. Always returns
   * true unless created using the constructor MethodInfo(Method, Class<?>);
   * 
   * @return True if this method was inherited. False otherwise.
   */
  public/*@ pure */boolean isInherited() {
    return my_is_inherited;
  }

}

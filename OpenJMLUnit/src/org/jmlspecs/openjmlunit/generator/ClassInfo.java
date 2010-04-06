/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "April 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * A wrapper for a Class object that represents the Class in terms
 * of ClassInfo and MethodInfo objects.
 * @author Jonathan Hogins
 */
public class ClassInfo {
  /**
   * The class object for this class.
   */
  private final Class<?> my_class;
  /**
   * The MethodInfo objects or the methods of this class.
   */
  private final ArrayList<MethodInfo> my_method_infos;

  /**
   * Constructor for a ClassInfo object for class the_class
   * 
   * @param the_class The class that this ClassInfo should represent.
   */
  public ClassInfo(Class<?> the_class) {
    my_class = the_class;
    Method[] methods = the_class.getMethods();
    my_method_infos = new ArrayList<MethodInfo>(methods.length);
    for (Method m : methods) {
      my_method_infos.add(new MethodInfo(m, the_class));
    }
  }

  /**
   * Returns the name of the class.
   * 
   * @return The name of the class
   */
  public/* @pure */String getName() {
    return my_class.getName();
  }

  /**
   * Returns the protection level of the class. Currently, the return value
   * is an integer representation the class' modifiers. To decode, use the
   * Modifier class.
   * 
   * @return The protection level of the class.
   */
  public/* @pure */int getProtectionLevel() {
    return my_class.getModifiers();
  }

  /**
   * Returns the class represented by this object.
   * 
   * @return The class passed into this object's constructor.
   */
  public/* @ pure */Class<?> getRepresentedClass() {
    return my_class;
  }

  // "What is the info for the class's parent class?",
  /**
   * Returns the ClassInfo object for the class' super-class.
   * 
   * @return The ClassInfo for the class' super-class.
   */
  /*
   * @ \result
   */
  public/* @pure */ClassInfo getSuperClassInfo() {
    return new ClassInfo(my_class.getSuperclass());
  }

  // "Is the class abstract?",
  /**
   * Returns true if the class is abstract, false otherwise.
   * 
   * @return True if the class is abstract, false otherwise.
   */
  /* @ \result == (getRepresentedClass().getModifiers() && Modifiers.ABSTRACT) */
  public/* @ pure */boolean isAbstract() {
    return (my_class.getModifiers() & Modifier.ABSTRACT) > 0;
  }

  // "What are the constructors?",
  // "What are the factory methods?",
  /**
   * Returns a List of MethodInfo objects that represent the factory methods of
   * the class.
   * 
   * @return A List of MethodInfo objects.
   */
  /*
   * @ (\foreach MethodInfo m; \result.contains(m); m.isFactory())
   */
  public List<MethodInfo> getFactoryMethods() {
    List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (m.isFactory()) {
        result.add(m);
      }
    }
    return result;
  }

  // "What are the non-factory static methods?",
  /**
   * Returns a List of MethodInfo objects that represent the non-factory static
   * methods of the class.
   * 
   * @return A List of MethodInfo objects.
   */
  /*
   * @ (\foreach MethodInfo m; \result.contains(m);
   * @    m.isStatic() && !m.isFactory)
   */
  public List<MethodInfo> getNonFactoryStaticMethods() {
    List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (m.isStatic() && !m.isFactory()) {
        result.add(m);
      }
    }
    return result;
  }

  // "What are the inherited instance methods?",
  /**
   * Returns a List of MethodInfo objects that represent the inherited methods
   * of the class.
   * 
   * @return A List of MethodInfo objects.
   */
  /* @ (\foreach MethodInfo m; \result.contains(m); m.isInherited())
   */
  public List<MethodInfo> getInheritedMethods() {
    List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (m.isInherited()) {
        result.add(m);
      }
    }
    return result;
  }
  // "What are the non-inherited instance methods?",
  /**
   * Returns a List of MethodInfo objects that represent the non-inherited methods
   * of the class.
   * 
   * @return A List of MethodInfo objects.
   */
  /* @ (\foreach MethodInfo m; \result.contains(m); !m.isInherited())
   */
  public List<MethodInfo> getNonInheritedMethods() {
    List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (!m.isInherited()) {
        result.add(m);
      }
    }
    return result;
  }

  // "What are the testable methods?"
  /**
   * Returns a List of MethodInfo objects that represent the testable methods
   * of the class. For a definition of testable, see MethodInfo.isTestable().
   * 
   * @return A List of MethodInfo objects.
   */
  /* @ (\foreach MethodInfo m; \result.contains(m); !m.isInherited())
   */
  public List<MethodInfo> getTestableMethods() {
    List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (!m.isTestable()) {
        result.add(m);
      }
    }
    return result;
  }
  // constraint
  // "The info for the parent class is null if and only if the class \
  // \ is 'java.lang.Object'.",
  // "There is at least one constructor."

}

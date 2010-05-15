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

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Information about a class under test.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public class ClassInfo extends TypeInfo {
  /*@ invariant my_short_name.equals(
    @   getFullyQualifiedName().substring(getFullyQualifiedName().lastIndexOf('.') + 1));
   */
  /**
   * The parent ClassInfo object.
   */
  private final ClassInfo my_parent;
  /**
   * The ProtectionLevel of this class.
   */
  private final ProtectionLevel my_protection_level;
  /**
   * Is this class abstract?
   */
  private final boolean my_is_abstract;
  /*@ invariant (\exists MethodInfo m; my_method_infos.contains(m);
    @           m.isConstructor()); */
  /**
   * The MethodInfo objects or the methods of this class.
   */
  private final List<MethodInfo> my_method_infos;

  /**
   * Constructor for a ClassInfo object given the describing parameters. For use
   * by factory classes.
   * 
   * @param the_name The fully qualified name of the class.
   * @param the_protection_level The protection level of the class.
   * @param the_is_abstract Is this class abstract?
   * @param the_method_infos The methods of this class.
   * @param the_parent The ClassInfo object for this class' parent. May be null
   *          only if the class name is java.lang.Object.
   */
  //@ requires the_parent == null ==> the_name.equals("java.lang.Object");
  protected ClassInfo(final String the_name, final ProtectionLevel the_protection_level,
                      final boolean the_is_abstract, final List<MethodInfo> the_method_infos,
                      final/*@ nullable */ClassInfo the_parent) {
    super(the_name);
    my_protection_level = the_protection_level;
    my_is_abstract = the_is_abstract;
    my_method_infos = Collections.unmodifiableList(the_method_infos);
    my_parent = the_parent;
  }

  /**
   * Returns the ClassInfo for this ClassInfo's parent. Returns null if
   * this ClassInfo represents java.lang.Object.
   * @return This ClassInfo's parent.
   */
  public/*@pure*/ClassInfo getParent() {
    return my_parent;
  }

  /**
   * Returns the protection level of the class.
   * 
   * @return The protection level of the class.
   */
  public/*@pure */ProtectionLevel getProtectionLevel() {
    return my_protection_level;
  }

  // "What is the info for the class's Superclass?",
  /**
   * Returns the ClassInfo object for the class' Superclass.
   * 
   * @return The ClassInfo for the class' Superclass.
   */
  public/*@pure */ClassInfo getSuperclassInfo() {
    return my_parent;
  }

  /**
   * Returns true if the class is abstract, false otherwise.
   * 
   * @return True if the class is abstract, false otherwise.
   */
  public/*@ pure */boolean isAbstract() {
    return my_is_abstract;
  }
  
  // "What are the constructors?",
  // "What are the factory methods?",
  /**
   * Returns a List of MethodInfo objects that represent the factory methods of
   * the class.
   * 
   * @return A List of MethodInfo objects.
   */
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isFactory()); */
  public List<MethodInfo> getFactoryMethods() {
    final List<MethodInfo> result = new LinkedList<MethodInfo>();
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
  /*@ ensures (\forall MethodInfo m; \result.contains(m);
    @           m.isStatic() && !m.isFactory()); */
  public List<MethodInfo> getNonFactoryStaticMethods() {
    final List<MethodInfo> result = new LinkedList<MethodInfo>();
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
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isInherited()); */
  public List<MethodInfo> getInheritedMethods() {
    final List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (m.isInherited()) {
        result.add(m);
      }
    }
    return result;
  }

  // "What are the non-inherited instance methods?",
  /**
   * Returns a List of MethodInfo objects that represent the non-inherited
   * methods of the class.
   * 
   * @return A List of MethodInfo objects.
   */
  /*@ ensures (\forall MethodInfo m; \result.contains(m); !m.isInherited()); */
  public List<MethodInfo> getNonInheritedMethods() {
    final List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (!m.isInherited()) {
        result.add(m);
      }
    }
    return result;
  }

  // "What are the testable methods?"
  /**
   * Returns a List of MethodInfo objects that represent the testable methods of
   * the class. For a definition of testable, see MethodInfo.isTestable().
   * 
   * @return A List of MethodInfo objects.
   */
  /*@ ensures (\forall MethodInfo m; \result.contains(m); !m.isInherited()); */
  public List<MethodInfo> getTestableMethods() {
    final List<MethodInfo> result = new LinkedList<MethodInfo>();
    for (MethodInfo m : my_method_infos) {
      if (m.isTestable()) {
        result.add(m);
      }
    }
    return result;
  }

}

/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.generator;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * Information about a class under test.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version August 2010
 */
public class ClassInfo extends TypeInfo {
  /**  
   * True if the methods of this class have been initialized,
   * false otherwise.
   */
  private boolean my_initialized = false;
  
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
    
  /**
   * Is this class an enum?
   */
  private final boolean my_is_enumeration;
  
  /**
   * The MethodInfo objects representing the methods of this class.
   */
  private final Set<MethodInfo> my_methods;
  /*@ private invariant 
    @    initialized ==> 
    @      (\exists MethodInfo m; my_method_infos.contains(m);
    @       m.isConstructor());
    @*/

  /**
   * The MethodInfo objects representing the inherited methods of this class.
   */
  private final Set<MethodInfo> my_inherited_methods;
  
  /**
   * The MethodInfo objects representing the overriding methods of this class.
   */
  private final Set<MethodInfo> my_overriding_methods;
  
  /**
   * The MethodInfo objects representing the overridden methods of this class.
   */
  private final Set<MethodInfo> my_overridden_methods;
  
  /**
   * Constructor for a ClassInfo object given the describing parameters. For use
   * by factory classes.
   * 
   * @param the_name The fully qualified name of the class.
   * @param the_protection_level The protection level of the class.
   * @param the_is_abstract Is this class abstract?
   * @param the_parent The ClassInfo object for this class' parent. May be null
   *          only if the class name is java.lang.Object.
   */
  //@ requires the_parent == null ==> the_name.equals("java.lang.Object");
  protected ClassInfo(final String the_name, 
                      final ProtectionLevel the_protection_level,
                      final boolean the_is_abstract, 
                      final boolean the_is_enumeration,
                      final /*@ nullable @*/ ClassInfo the_parent) {
    super(the_name);
    my_protection_level = the_protection_level;
    my_is_abstract = the_is_abstract;
    my_is_enumeration = the_is_enumeration;
    my_methods = new HashSet<MethodInfo>();
    my_inherited_methods = new HashSet<MethodInfo>();
    my_overriding_methods = new HashSet<MethodInfo>();
    my_overridden_methods = new HashSet<MethodInfo>();
    my_parent = the_parent;
  }

  /**
   * Initializes the methods of this ClassInfo. This method may only
   * be called once.
   */
  //@ requires !isInitialized();
  /*@ requires (\exists MethodInfo m; the_methods.contains(m); 
    @           m.isConstructor());
    @*/
  //@ ensures isInitialized();
  public void initializeMethods(final Set<MethodInfo> the_methods) {
    my_methods.clear();
    my_methods.addAll(the_methods);
    
    // inherited methods
    my_inherited_methods.clear();
    for (MethodInfo m : my_methods) {
      if (m.isInherited()) {
        my_inherited_methods.add(m);
      }
    }
      
    // overriding methods
    my_overriding_methods.clear();
    final Set<String> signatures = new HashSet<String>();
    final Set<MethodInfo> non_inherited = new HashSet<MethodInfo>(my_methods);
    non_inherited.removeAll(my_inherited_methods);
    
    for (MethodInfo m : my_inherited_methods) {
      signatures.add(m.toString());
    }
    for (MethodInfo m : non_inherited) {
      if (signatures.contains(m.toString())) {
        // m overrides an inherited method
        my_overriding_methods.add(m);
      }
    }
    
    // overridden methods
    my_overridden_methods.clear();
    signatures.clear();
    for (MethodInfo m : my_overriding_methods) {
      signatures.add(m.toString());
    }
    for (MethodInfo m : my_inherited_methods) {
      if (signatures.contains(m.toString())) {
        // m is overridden by another method
        my_overridden_methods.add(m);
      }
    }
    
    my_initialized = true;
  }
  
  /**
   * @return the ClassInfo for this class's parent, or null if
   * this ClassInfo represents java.lang.Object.
   */
  public /*@pure*/ ClassInfo getParent() {
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

  /**
   * Returns true if the class is abstract, false otherwise.
   * 
   * @return True if the class is abstract, false otherwise.
   */
  public/*@ pure */boolean isAbstract() {
    return my_is_abstract;
  }
  
  /**
   * @return true if the class is an enumeration, false otherwise.
   */
  public /*@ pure @*/ boolean isEnumeration() {
    return my_is_enumeration;
  }
  
  /**
   * @returns true if the methods have been initialized, 
   * false otherwise.
   */
  public /*@ pure @*/ boolean isInitialized() {
    return my_initialized;
  }
  
  /**
   * Returns a Set of MethodInfo objects that represent the factory methods of
   * the class.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isFactory()); */
  public /*@ pure @*/  Set<MethodInfo> getFactoryMethods() {
    final Set<MethodInfo> result = new HashSet<MethodInfo>();
    for (MethodInfo m : my_methods) {
      if (m.isFactory()) {
        result.add(m);
      }
    }
    return result;
  }

  /**
   * @return a Set of MethodInfo objects that represent the non-factory static
   * methods of the class.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m);
    @           m.isStatic() && !m.isFactory()); */
  public /*@ pure @*/ Set<MethodInfo> getNonFactoryStaticMethods() {
    final Set<MethodInfo> result = new HashSet<MethodInfo>();
    for (MethodInfo m : my_methods) {
      if (m.isStatic() && !m.isFactory()) {
        result.add(m);
      }
    }
    return result;
  }

  /**
   * @return a Set of MethodInfo objects that represent the inherited methods
   * of the class.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isInherited()); */
  public /*@ pure @*/ Set<MethodInfo> getInheritedMethods() {
    return Collections.unmodifiableSet(my_inherited_methods);
  }

  /**
   * @return a Set of MethodInfo objects that represent the non-inherited
   * methods of the class.
   * 
   * @return A Set of MethodInfo objects.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); !m.isInherited()); */
  public /*@ pure @*/ Set<MethodInfo> getNonInheritedMethods() {
    final Set<MethodInfo> result = new HashSet<MethodInfo>(my_methods);
    result.removeAll(my_inherited_methods);
    return Collections.unmodifiableSet(result);
  }

  /**
   * @return a Set of MethodInfo objects that represent the methods of
   * the class that override inherited methods.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); !m.isInherited()); */
  public /*@ pure @*/ Set<MethodInfo> getOverridingMethods() {
    return Collections.unmodifiableSet(my_overriding_methods);
  }

  /**
   * @return a Set of MethodInfo objects that represent the inherited 
   * methods of the class that are overridden.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isInherited()); */
  public /*@ pure @*/ Set<MethodInfo> getOverriddenMethods() {
    return Collections.unmodifiableSet(my_overridden_methods);
  }

  // "What are the testable methods?"
  /**
   * Returns a Set of MethodInfo objects that represent the testable methods of
   * the class. For a definition of testable, see MethodInfo.isTestable().
   * 
   * @return A Set of MethodInfo objects.
   */
  //@ requires isInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isTestable()); */
  public /*@ pure @*/ Set<MethodInfo> getTestableMethods() {
    final Set<MethodInfo> result = new HashSet<MethodInfo>();
    for (MethodInfo m : my_methods) {
      if (m.isTestable() && !my_overridden_methods.contains(m)) {
        // we don't add overridden methods to the testable set
        result.add(m);
      }
    }
    return result;
  }

  /**
   * @return a Set of MethodInfo objects that represent the 
   * methods of the class.
   */
  //@ requires isInitialized();
  public /*@ pure @*/ Set<MethodInfo> getMethods() {
    return Collections.unmodifiableSet(my_methods);
  }
}

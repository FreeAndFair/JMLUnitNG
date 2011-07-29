/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.generator;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.jmlspecs.jmlunitng.util.ProtectionLevel;

/**
 * Information about a class under test.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version July 2011
 */
public class ClassInfo extends TypeInfo {
  /**  
   * True if the methods of this class have been initialized,
   * false otherwise.
   */
  private boolean my_methods_initialized;
  
  /**
   * True if the literals of this class have been initialized,
   * false otherwise.
   */
  private boolean my_literals_initialized;
  
  /**
   * The parent ClassInfo object.
   */
  private final ClassInfo my_parent;

  /**
   * The ClassInfo objects for the interfaces.
   */
  private final SortedSet<ClassInfo> my_interfaces;
  
  /**
   * The ProtectionLevel of this class.
   */
  private final ProtectionLevel my_protection_level;
  
  /**
   * Is this class abstract (an abstract class or interface)?
   */
  private final boolean my_is_abstract;
    
  /**
   * Is this class an interface?
   */
  private final boolean my_is_interface;
  
  /**
   * Is this class an enum?
   */
  private final boolean my_is_enumeration;
  
  /**
   * Is this class static?
   */
  private final boolean my_is_static;
  
  /**
   * Is this class inner?
   */
  private final boolean my_is_inner;
  
  /**
   * The ClassInfo objects representing the inner classes of this class.
   */
  private final Set<ClassInfo> my_nested_classes;
  
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
   * The map from classes to literals declared in this class.
   */
  private final Map<String, SortedSet<String>> my_literals;
  
  /**
   * The map from classes to literals declared in the specs for this class.
   */
  private final Map<String, SortedSet<String>> my_spec_literals;
  
  /**
   * Constructor for a ClassInfo object given the describing parameters. For use
   * by factory classes.
   * 
   * @param the_name The fully qualified name of the class.
   * @param the_protection_level The protection level of the class.
   * @param the_is_abstract Is this class abstract?
   * @param the_is_interface Is this class an interface?
   * @param the_is_enumeration Is this class an enumeration?
   * @param the_is_static Is this class static?
   * @param the_is_inner Is this an inner class? 
   * @param the_parent The ClassInfo object for this class' parent. May be null
   *          only if the class name is java.lang.Object.
   * @param the_interfaces The interfaces implemented by this class.
   */
  //@ requires the_parent == null ==> the_name.equals("java.lang.Object");
  protected ClassInfo(final String the_name, 
                      final ProtectionLevel the_protection_level,
                      final boolean the_is_abstract, 
                      final boolean the_is_interface,
                      final boolean the_is_enumeration,
                      final boolean the_is_static,
                      final boolean the_is_inner,
                      final /*@ nullable @*/ ClassInfo the_parent,
                      final SortedSet<ClassInfo> the_interfaces) {
    super(the_name);
    my_protection_level = the_protection_level;
    my_is_abstract = the_is_abstract;
    my_is_interface = the_is_interface;
    my_is_enumeration = the_is_enumeration;
    my_is_static = the_is_static;
    my_is_inner = the_is_inner;
    my_nested_classes = new HashSet<ClassInfo>();
    my_methods = new HashSet<MethodInfo>();
    my_inherited_methods = new HashSet<MethodInfo>();
    my_overriding_methods = new HashSet<MethodInfo>();
    my_overridden_methods = new HashSet<MethodInfo>();
    my_parent = the_parent;
    my_interfaces = new TreeSet<ClassInfo>(the_interfaces);
    my_literals = new HashMap<String, SortedSet<String>>();
    my_spec_literals = new HashMap<String, SortedSet<String>>();
  }

  /**
   * Initializes the nested classes of this ClassInfo.
   * 
   * @param the_classes The nested classes.
   */
  public void initializeNestedClasses(final Set<ClassInfo> the_classes) {
    my_nested_classes.addAll(the_classes);
  }
  
  /**
   * Initializes the literals of this ClassInfo (the literals declared
   * in this class and in its specifications). This method may only
   * be called once.
   * 
   * @param the_literals The literals to initialize this ClassInfo with.
   * @param the_spec_literals The spec literals to initialize this ClassInfo
   * with.
   */
  //@ requires !areLiteralsInitialized();
  //@ ensures areLiteralsInitialized();
  public void 
  initializeLiterals(final Map<String, SortedSet<String>> the_literals,
                     final Map<String, SortedSet<String>> the_spec_literals) {
    for (Map.Entry<String, SortedSet<String>> e : the_literals.entrySet()) {
      final SortedSet<String> new_set = new TreeSet<String>(e.getValue());
      my_literals.put(e.getKey(), Collections.unmodifiableSortedSet(new_set));
    }
    for (Map.Entry<String, SortedSet<String>> e : the_spec_literals.entrySet()) {
      final SortedSet<String> new_set = new TreeSet<String>(e.getValue());
      my_spec_literals.put(e.getKey(), Collections.unmodifiableSortedSet(new_set));
    }
    my_literals_initialized = true;
  }
  
  /**
   * Initializes the methods of this ClassInfo. This method may only
   * be called once.
   * 
   * @param the_methods The methods to initialize this ClassInfo with.
   */
  //@ requires !areMethodsInitialized();
  /*@ requires (\exists MethodInfo m; the_methods.contains(m); 
    @           m.isConstructor());
    @*/
  //@ ensures areMethodsInitialized();
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
    
    my_methods_initialized = true;
  }
  
  /**
   * @return the ClassInfo for this class's parent, or null if
   * this ClassInfo represents java.lang.Object.
   */
  public /* @pure */ ClassInfo getParent() {
    return my_parent;
  }

  /**
   * @return the set of ClassInfos for this class's interfaces.
   */
  public /*@ pure @*/ SortedSet<ClassInfo> getInterfaces() {
    return Collections.unmodifiableSortedSet(my_interfaces);
  }
  
  /**
   * Returns the protection level of the class.
   * 
   * @return The protection level of the class.
   */
  public /* @pure */ ProtectionLevel getProtectionLevel() {
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
  public /*@ pure @*/ boolean isInterface() {
    return my_is_interface;
  }
  
  /**
   * @return true if the class is an enumeration, false otherwise.
   */
  public /*@ pure @*/ boolean isEnumeration() {
    return my_is_enumeration;
  }
  
  /**
   * @return true if the class is a static class, false otherwise.
   */
  public /*@ pure @*/ boolean isStatic() {
    return my_is_static;
  }
  
  /**
   * @return true if the class is an inner class, false otherwise.
   */
  public /*@ pure @*/ boolean isInner() {
    return my_is_inner;
  }
  
  /**
   * @return true if the literals have been initialized, 
   * false otherwise.
   */
  public /*@ pure @*/ boolean areLiteralsInitialized() {
    return my_literals_initialized;
  }
  
  /**
   * @return true if the methods have been initialized, 
   * false otherwise.
   */
  public /*@ pure @*/ boolean areMethodsInitialized() {
    return my_methods_initialized;
  }

  /**
   * Returns a Set of MethodInfo objects that represent the factory methods of
   * the class.
   */
  //@ requires areMethodsInitialized();
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
  //@ requires areMethodsInitialized();
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
  //@ requires areMethodsInitialized();
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
  //@ requires areMethodsInitialized();
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
  //@ requires areMethodsInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); !m.isInherited()); */
  public /*@ pure @*/ Set<MethodInfo> getOverridingMethods() {
    return Collections.unmodifiableSet(my_overriding_methods);
  }

  /**
   * @return a Set of MethodInfo objects that represent the inherited 
   * methods of the class that are overridden.
   */
  //@ requires areMethodsInitialized();
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
  //@ requires areMethodsInitialized();
  /*@ ensures (\forall MethodInfo m; \result.contains(m); m.isTestable()); */
  public /*@ pure @*/ Set<MethodInfo> getTestableMethods() {
    final Set<MethodInfo> result = new HashSet<MethodInfo>();
    for (MethodInfo m : my_methods) {
      if (m.isTestable() && !my_overridden_methods.contains(m) &&
          (!isAbstract() || m.isStatic())) {
        // we don't add overridden methods, or instance methods of abstract classes,
        // to the testable set
        result.add(m);
      }
    }
    return result;
  }

  /**
   * @return a Set of MethodInfo objects that represent the 
   * methods of the class.
   */
  //@ requires areMethodsInitialized();
  public /*@ pure @*/ Set<MethodInfo> getMethods() {
    return Collections.unmodifiableSet(my_methods);
  }
  
  /**
   * Checks for uniqueness of abbreviated formatted method names.
   * 
   * @param the_method The method to check.
   * @return true if the abbreviated name of the specified method is 
   * unique within this class, false otherwise. If the specified method
   * is not within this class, the result is true.
   */
  //@ requires areMethodsInitialized();
  public /*@ pure @*/ boolean isAbbreviatedNameUnique
  (final MethodInfo the_method) {
    boolean result = true;
    if (my_methods.contains(the_method)) {
      final String abbrev_name = the_method.getAbbreviatedFormattedName();
      for (MethodInfo m : my_methods) {
        if (!m.equals(the_method)) {
          result &= !m.getAbbreviatedFormattedName().equals(abbrev_name);
        }
      }
    }
    return result;
  }
  
  /**
   * @return a Set of MethodInfo objects that represent the
   * constructors of this class.
   */
  //@ requires areMethodsInitialized();
  //@ ensures (\forall MethodInfo m; \result.contains(m); m.isConstructor());
  public /*@ pure @*/ Set<MethodInfo> getConstructors() {
    final Set<MethodInfo> constructors = new HashSet<MethodInfo>();
    for (MethodInfo m : my_methods) {
      if (m.isConstructor()) {
        constructors.add(m);
      }
    }
    return Collections.unmodifiableSet(constructors);
  }
  
  /**
   * @return a set of ClassInfo objects that represent the
   * nested classes of this class.
   */
  public /*@ pure @*/ Set<ClassInfo> getNestedClasses() {
    return Collections.unmodifiableSet(my_nested_classes);
  }
  
  /**
   * Retrieve the literals of the specified class declared in 
   * this class. Note that this does <i>not</i> include any literals 
   * declared in methods or method specs within this class; those 
   * must be retrieved from the appropriate MethodInfo objects.
   *
   * @param the_class The class for which to get the literals.
   * @return A set of literals for the specified class, or 
   * the empty set no literals exist for the class.
   */
  //@ requires areLiteralsInitialized();
  public /*@ pure @*/ SortedSet<String> 
  getLiterals(final String the_class) {
    final SortedSet<String> result = new TreeSet<String>();  
    if (my_literals.get(the_class) != null) {
      result.addAll(my_literals.get(the_class));
    }
    return result;
  }
  
  /**
   * Retrieve the literals of the specified class declared in 
   * the specifications of this class. Note that this does <i>not</i> 
   * include any literals declared in methods or method specs within 
   * this class; those must be retrieved from the appropriate 
   * MethodInfo objects.
   *
   * @param the_class The class for which to get the literals.
   * @return A set of literals for the specified class, or 
   * the empty set if no literals exist for the class.
   */
  //@ requires areLiteralsInitialized();
  public /*@ pure @*/ SortedSet<String> 
  getSpecLiterals(final String the_class) {
    final SortedSet<String> result = new TreeSet<String>();  
    if (my_spec_literals.get(the_class) != null) {
      result.addAll(my_spec_literals.get(the_class));
    }
    return result;
  }
  
  /**
   * Retrieve the entire map of literals declared in this class.
   * 
   * @return An unmodifiable view of the map of literals.
   */
  public /*@ pure @*/ Map<String, SortedSet<String>> getLiterals() {
    return Collections.unmodifiableMap(my_literals);
  }

  /**
   * Retrieve the entire map of literals declared in this class's
   * specification.
   * 
   * @return An unmodifiable view of the map of literals.
   */
  public /*@ pure @*/ Map<String, SortedSet<String>> getSpecLiterals() {
    return Collections.unmodifiableMap(my_spec_literals);
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean equals(final /*@ nullable @*/ Object the_other) {
    boolean result = super.equals(the_other);

    if (result && the_other != this) {
      final ClassInfo cls = (ClassInfo) the_other;
      result &= my_methods_initialized == cls.my_methods_initialized;
      result &= my_interfaces.equals(cls.my_interfaces);
      result &= my_protection_level.equals(cls.my_protection_level);
      result &= my_is_abstract == cls.my_is_abstract;
      result &= my_is_interface == cls.my_is_interface;
      result &= my_is_enumeration == cls.my_is_enumeration;
      result &= my_nested_classes.equals(cls.my_nested_classes);
      result &= my_methods.equals(cls.my_methods);
      result &= my_inherited_methods.equals(cls.my_inherited_methods);
      result &= my_overriding_methods.equals(cls.my_overriding_methods);
      result &= my_overridden_methods.equals(cls.my_overridden_methods);
    }

    return result;
  }
  
  /**
   * {@inheritDoc}
   */
  public int hashCode() {
    return toString().hashCode();
  }
}

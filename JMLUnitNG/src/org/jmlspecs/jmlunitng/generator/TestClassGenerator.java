/*
 * JMLUnitNG 
 * Copyright (C) 2010-12
 */

package org.jmlspecs.jmlunitng.generator;

import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.jmlspecs.jmlunitng.JMLUnitNG;
import org.jmlspecs.jmlunitng.JMLUnitNGConfiguration;
import org.jmlspecs.jmlunitng.util.Logger;
import org.jmlspecs.jmlunitng.util.ProtectionLevel;
import org.jmlspecs.jmlunitng.util.StringTemplateUtil;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;

/**
 * Generator for classes that contain unit tests.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public class TestClassGenerator {
  /**
   * Valid RAC versions.
   */
  public static final List<String> VALID_RAC_VERSIONS;
  
  static {
    final List<String> temp = new ArrayList<String>();
    temp.add("jml4");
    temp.add("jml2");
    temp.add("openjml");
    VALID_RAC_VERSIONS = Collections.unmodifiableList(temp);
  }
    
  /**
   * The default max protection level.
   */
  public static final ProtectionLevel DEF_PROTECTION_LEVEL = ProtectionLevel.PUBLIC;
  
  /**
   * Are inherited methods tested by default?
   */
  public static final boolean DEF_TEST_INHERITED_METHODS = false;
  
  /**
   * Are deprecated methods tested by default?
   */
  public static final boolean DEF_TEST_DEPRECATED_METHODS = false;
  
  /**
   * Do test data classes use reflection by default?
   */
  public static final boolean DEF_USE_REFLECTION = true;

  /**
   * Do test data classes use children by default?
   */
  public static final boolean DEF_USE_CHILDREN = true;
  
  /**
   * The default RAC version to generate tests for.
   */
  public static final String DEF_RAC_VERSION = "openjml";
  
  /**
   * The line max line width of generated code.
   */
  public static final int LINE_WIDTH = 120;

  /**
   * The configuration to use for generating classes.
   */
  private final JMLUnitNGConfiguration my_config;
  
  /**
   * The logger to use for printing output.
   */
  private final Logger my_logger;
  
  /**
   * The set of files we have created.
   */
  private final Set<String> my_created_files = new HashSet<String>();
  
  /**
   * Create a new TestClassGenerator with the default options.
   */
  public TestClassGenerator() {
    this(new JMLUnitNGConfiguration(), new Logger(false));
  }

  /**
   * Create a new TestClassGenerator with the given configuration
   * and logger.
   * 
   * @param the_config The JMLUnitNGConfiguration to use.
   * @param the_logger The logger to use to generate output.
   */
  public TestClassGenerator(final JMLUnitNGConfiguration the_config,
                            final Logger the_logger) {
    my_config = the_config;
    my_logger = the_logger;
  }

  /**
   * Generates a local strategy class for the specified method parameter.
   * 
   * @param the_class The class to generate a strategy class for.
   * @param the_method The method to generate a strategy class for.
   * @param the_param The parameter to generate a strategy class for.
   * @param the_writer The writer to write the strategy class to.
   * @throws IOException if an IOException occurs while writing the class.
   */
  //@ requires the_class.getMethods().contains(the_method);
  //@ requires the_method.getParameters().contains(the_param);
  public void generateLocalStrategyClass(final /*@ non_null @*/ ClassInfo the_class,
                                         final /*@ non_null @*/ MethodInfo the_method,
                                         final /*@ non_null @*/ ParameterInfo the_param, 
                                         final /*@ non_null @*/ Writer the_writer)
    throws IOException {
    final STGroup group = StringTemplateUtil.load("strategy_local");
    final ST t = group.getInstanceOf("main");
    final SortedSet<String> children = new TreeSet<String>();
    final SortedSet<String> literals = new TreeSet<String>();
    final String fq_name = the_param.getType().getFullyQualifiedName();
    final ClassInfo type_class_info = InfoFactory.getClassInfo(fq_name);
    
    // if "--children" was set, we use all child classes we are currently analyzing
    if (my_config.isChildrenSet() && type_class_info != null) {
      children.addAll(getChildrenFromClassInfo(type_class_info));
    }

    // if "--literals" or "--spec-literals" was set, we use all child classes
    // identified as literals for the method under test
    
    if (my_config.isLiteralsSet() && type_class_info != null) {
      children.addAll(checkChildLiterals(type_class_info, 
                      the_method.getLiterals(Class.class.getName())));
    }
    if (my_config.isSpecLiteralsSet() && type_class_info != null) {
      children.addAll(checkChildLiterals(type_class_info, 
                      the_method.getSpecLiterals(Class.class.getName())));
    }
    
    // add literals for this type 
    
    if (my_config.isLiteralsSet()) {
      literals.addAll(the_method.getLiterals(fq_name));
    }
    if (my_config.isSpecLiteralsSet()) {
      literals.addAll(the_method.getSpecLiterals(fq_name));
    }
    
    t.add("class", the_class);
    t.add("date", getFormattedDate());
    t.add("method", the_method);
    t.add("param", the_param);
    t.add("literals", literals);
    t.add("jmlunitng_version", JMLUnitNG.version());
    t.add("use_reflection", my_config.isReflectionSet());
    t.add("children", children);
    
    if (!my_config.isNoGenSet()) {
      my_logger.println("Generating local strategy for parameter " + the_param.getName() + 
                        " of " + the_method);
    }
    
    the_writer.write(t.render(LINE_WIDTH));
  }
  
  /**
   * Generates a class-scope strategy class for the specified type.
   * 
   * @param the_class The class to generate a strategy class for.
   * @param the_type The type to generate a strategy class for.
   * @param the_writer The writer to write the strategy class to.
   * @throws IOException if an IOException occurs while writing the class.
   */
  //@ requires the_class.getMethods().contains(the_method);
  //@ requires the_method.getParameters().contains(the_param);
  public void generateClassStrategyClass(final /*@ non_null @*/ ClassInfo the_class,
                                         final /*@ non_null @*/ TypeInfo the_type,
                                         final /*@ non_null @*/ Writer the_writer)
    throws IOException {
    final STGroup group = StringTemplateUtil.load("strategy_class");
    final ST t = group.getInstanceOf("main");
    final SortedSet<String> children = new TreeSet<String>();
    final SortedSet<String> literals = new TreeSet<String>();
    final String fq_name = the_type.getFullyQualifiedName();
    final ClassInfo type_class_info = InfoFactory.getClassInfo(fq_name);

    // if "--children" was set, we use all child classes we are currently analyzing
    if (my_config.isChildrenSet() && type_class_info != null) {
      children.addAll(getChildrenFromClassInfo(type_class_info));
    }

    // if "--literals" or "--spec-literals" was set, we use all child classes
    // identified as literals for the method under test
    
    if (my_config.isLiteralsSet() && type_class_info != null) {
      children.addAll(checkChildLiterals(type_class_info, 
                      the_class.getLiterals(Class.class.getName())));
    }
    if (my_config.isSpecLiteralsSet() && type_class_info != null) {
      children.addAll(checkChildLiterals(type_class_info, 
                      the_class.getSpecLiterals(Class.class.getName())));
    }
    
    // add literals for this type
    
    if (my_config.isLiteralsSet()) {
      literals.addAll(the_class.getLiterals(fq_name));
    }
    if (my_config.isSpecLiteralsSet()) {
      literals.addAll(the_class.getSpecLiterals(fq_name));
    }
    
    t.add("class", the_class);
    t.add("date", getFormattedDate());
    t.add("type", the_type);
    t.add("literals", literals);
    t.add("jmlunitng_version", JMLUnitNG.version());
    t.add("use_reflection", my_config.isReflectionSet());
    t.add("children", children);

    if (!my_config.isNoGenSet()) {
      my_logger.println("Generating class strategy for type " +
                        the_type.getFullyQualifiedName());
    }
    
    the_writer.write(t.render(LINE_WIDTH));
  }
  
  /**
   * Generates a package-scope strategy class for the specified type.
   * 
   * @param the_class The class to generate a strategy class for.
   * @param the_type The type to generate a strategy class for.
   * @param the_writer The writer to write the strategy class to.
   * @throws IOException if an IOException occurs while writing the class.
   */
  //@ requires the_class.getMethods().contains(the_method);
  //@ requires the_method.getParameters().contains(the_param);
  public void generatePackageStrategyClass(final /*@ non_null @*/ ClassInfo the_class,
                                           final /*@ non_null @*/ TypeInfo the_type,
                                           final /*@ non_null @*/ Writer the_writer)
    throws IOException {
    final STGroup group = StringTemplateUtil.load("strategy_package");
    final ST t = group.getInstanceOf("main");
    final SortedSet<String> children = new TreeSet<String>();
    
    final ClassInfo type_class_info = 
      InfoFactory.getClassInfo(the_type.getFullyQualifiedName());

    // if "--children" was set, we use all child classes we are currently analyzing
    if (my_config.isChildrenSet() && type_class_info != null) {
      children.addAll(getChildrenFromClassInfo(type_class_info));
    }

    
    String pkg = null;
    if (the_class.isPackaged()) {
      pkg = the_class.getPackageName();
    }
    t.add("package", pkg);
    t.add("date", getFormattedDate());
    t.add("type", the_type);
    t.add("jmlunitng_version", JMLUnitNG.version());
    t.add("use_reflection", my_config.isReflectionSet());
    t.add("children", children);

    if (!my_config.isNoGenSet()) {
      my_logger.println("Generating package strategy for type " +
                        the_type.getFullyQualifiedName());
    }
    
    the_writer.write(t.render(LINE_WIDTH));
  }
  
  /**
   * Generates the instance strategy class for the specified class.
   * 
   * @param the_class The class to generate a strategy class for.
   * @param the_writer The writer to write the strategy class to.
   * @throws IOException if an IOException occurs while writing the class.
   */
  //@ requires the_class.getMethods().contains(the_method);
  //@ requires the_method.getParameters().contains(the_param);
  public void generateInstanceStrategyClass(final /*@ non_null @*/ ClassInfo the_class,
                                            final /*@ non_null @*/ Writer the_writer)
    throws IOException {
    final STGroup group = StringTemplateUtil.load("strategy_instance");
    final ST t = group.getInstanceOf("main");
    
    t.add("class", the_class);
    t.add("date", getFormattedDate());
    t.add("jmlunitng_version", JMLUnitNG.version());
    t.add("use_reflection", my_config.isReflectionSet());
    
    if (!my_config.isNoGenSet()) {
      my_logger.println("Generating instance strategy for class " +
                        the_class.getFullyQualifiedName());
    }
    
    the_writer.write(t.render(LINE_WIDTH));
  }
  
  /**
   * Generates a test class for the_class and writes it to the_writer. 
   * 
   * @param the_class The class to generate a test class for.
   * @param the_methods The methods to generate tests for. 
   * @param the_writer The writer to write the test class to.
   * @throws IOException if an IOException occurs while writing the class.
   */
  /*@ requires (\forall MethodInfo m; the_methods.contains(m); 
    @           the_class.getMethods().contains(m));
    @*/
  public void generateTestClass(final /*@ non_null @*/ ClassInfo the_class,
                                final /*@ non_null @*/ Set<MethodInfo> the_methods,
                                final /*@ non_null @*/ Writer the_writer)
    throws IOException {
    final STGroup group = 
      StringTemplateUtil.load("test_class_" + my_config.getRACVersion());
    final ST t = group.getInstanceOf("main");
    t.add("class", the_class);
    t.add("date", getFormattedDate());
    t.add("methods", the_methods);
    
    // if there are no methods with parameters to generate tests for, 
    // we don't need a data package
    boolean params = false;
    for (MethodInfo m : the_methods) {
      params = params || !m.getParameters().isEmpty();
    }
    t.add("params", params);
    t.add("package_name", the_class.getPackageName());
    t.add("packaged", !"".equals(the_class.getPackageName()));
    t.add("parallel", my_config.isParallelSet());
    t.add("jmlunitng_version", JMLUnitNG.version());
    
    if (!my_config.isNoGenSet()) {
      my_logger.println("Generating test class for class " +
                        the_class.getFullyQualifiedName());
    }
    
    the_writer.write(t.render(LINE_WIDTH));
  }

  /**
   * Generates both test and test data classes and writes them to the given
   * directory.
   * 
   * @param the_class The class for which to generate test classes.
   * @param the_test_dir The directory in which to generate test classes, as well
   * as package and instance strategies.
   * @param the_strategy_dir The directory in which to generate parameter and class
   * strategies.
   * @throws IOException Thrown if an IOException occurs while generating the classes.
   */
  //@ requires VALID_RAC_VERSIONS.contains(the_rac);
  //@ requires (new File(the_dir)).isDirectory();
  public void generateClasses(final /*@ non_null @*/ ClassInfo the_class, 
                              final /*@ non_null @*/ String the_test_dir,
                              final /*@ non_null @*/ String the_strategy_dir) 
    throws IOException {
    final STGroup shared = StringTemplateUtil.load("shared_java");
    
    final Set<MethodInfo> methods_to_test = getMethodsToTest(the_class);
    final Set<ClassInfo> classes_to_test = getClassesToTest(the_class);
    
    // we don't test nested classes yet but we can say something
    for (ClassInfo c : classes_to_test) {
      my_logger.println("No test generation yet for nested class " + 
                        c.getFullyQualifiedName());
    }
    
    if (methods_to_test.isEmpty()) {
      my_logger.println("No testable methods in class " + the_class.getFullyQualifiedName());
      return;
    }
    
    // initialize name templates
    final ST tc_name = shared.getInstanceOf("testClassName");
    tc_name.add("classInfo", the_class);

    // this stream is for writing to memory, in the case of a dry run
    
    final ByteArrayOutputStream baos = new ByteArrayOutputStream();
    final BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(baos));

    File f;
    
    // generate the (single) test class, if necessary

    f = new File(the_test_dir + tc_name.render() + 
                 JMLUnitNG.JAVA_SUFFIX);
    if (my_config.isDryRunSet() || my_config.isNoGenSet()) {
      generateTestClass(the_class, methods_to_test, bw);
      baos.reset();
    } else {
      final FileWriter fw = new FileWriter(f);
      generateTestClass(the_class, methods_to_test, fw);
      fw.close();
    }
    my_created_files.add(f.getCanonicalPath());

    // generate the strategy classes - there are three stages here 
    // first: local-scope method parameter strategy classes, only if concrete

    for (MethodInfo m : methods_to_test) {
      for (ParameterInfo p : m.getParameters()) {
        final ST ls_name = shared.getInstanceOf("localStrategyName");
        ls_name.add("classInfo", the_class);
        ls_name.add("methodInfo", m);
        ls_name.add("paramInfo", p);
        f = new File(the_strategy_dir + ls_name.render() + 
                     JMLUnitNG.JAVA_SUFFIX);
        if (my_config.isDryRunSet() || my_config.isNoGenSet()) {
          generateLocalStrategyClass(the_class, m, p, bw);
          baos.reset();
        } else if (f.exists()) {
          my_logger.println("Not overwriting existing strategy for parameter " + 
                            p.getName() +  " of " + m); 
        } else { 
          final FileWriter fw = new FileWriter(f);
          generateLocalStrategyClass(the_class, m, p, fw);
          fw.close(); 
        }
        my_created_files.add(f.getCanonicalPath());
      }
    }

    // second: class-scope strategy classes for all data types, only if concrete

    final Set<TypeInfo> parameter_types = getUniqueParameterTypes(methods_to_test);
    
    for (TypeInfo t : parameter_types) {
      final ST gs_name = shared.getInstanceOf("classStrategyName");
      gs_name.add("classInfo", the_class);
      gs_name.add("typeInfo", t);
      f = new File(the_strategy_dir + gs_name.render() + 
                   JMLUnitNG.JAVA_SUFFIX);
      if (my_config.isDryRunSet() || my_config.isNoGenSet()) {
        generateClassStrategyClass(the_class, t, bw);
        baos.reset();
      } else if (f.exists()) {
        my_logger.println("Not overwriting existing global strategy " + 
                          "for type " + t.getFullyQualifiedName());        
      } else {
        final FileWriter fw = new FileWriter(f);
        generateClassStrategyClass(the_class, t, fw);
        fw.close();
      }
      my_created_files.add(f.getCanonicalPath());
    }
    
    // third: package strategy classes for all types for which strategies
    // were generated above (note that these may duplicate when we generate
    // multiple sets of tests in the same package, but that's OK, as
    // we won't overwrite them after the first one)
    
    for (TypeInfo t : parameter_types) {
      final ST ps_name = shared.getInstanceOf("packageStrategyName");
      ps_name.add("typeInfo", t);

      f = new File(the_test_dir + ps_name.render() + 
                   JMLUnitNG.JAVA_SUFFIX);
      if (my_config.isDryRunSet() || my_config.isNoGenSet()) {
        generatePackageStrategyClass(the_class, t, bw);
        baos.reset();
      } else if (f.exists()) {
        String pn = "<default>";
        if (the_class.isPackaged()) {
          pn = the_class.getPackageName();
        }
        my_logger.println("Not overwriting existing package strategy " +
                          "for type " + t.getFullyQualifiedName() + 
                          " in package " + pn);
      } else {
        final FileWriter fw = new FileWriter(f);
        generatePackageStrategyClass(the_class, t, fw);
        fw.close();
      } 
      my_created_files.add(f.getCanonicalPath());
    }

    // fourth: instance strategy class for this class
    
    final ST is_name = shared.getInstanceOf("instanceStrategyName");
    is_name.add("classInfo", the_class);
    f = new File(the_test_dir + is_name.render() + 
                 JMLUnitNG.JAVA_SUFFIX);
    if (my_config.isDryRunSet() || my_config.isNoGenSet()) {
      generateInstanceStrategyClass(the_class, bw);
      baos.reset();      
    } else if (f.exists()) {
      my_logger.println("Not overwriting existing instance strategy " + 
                        "for class " + the_class.getFullyQualifiedName());
    } else {
      final FileWriter fw = new FileWriter(f);
      generateInstanceStrategyClass(the_class, fw);
      fw.close();
    } 
    my_created_files.add(f.getCanonicalPath());
    
  }
  
  /**
   * @return an unmodifiable view of the set of files created by this
   * generator.
   */
  public /*@ pure @*/ Set<String> getCreatedFiles() {
    return Collections.unmodifiableSet(my_created_files);
  }
  
  /**
   * @return a formatted version of the current date and time.
   */
  private String getFormattedDate() {
    final SimpleDateFormat df = 
      new SimpleDateFormat("yyyy-MM-dd HH:mm Z", Locale.US);
    return df.format(new Date());
  }
  
  /**
   * Returns the methods from the given class to test based on generator
   * settings.
   * 
   * @param the_class The class for which to find testable methods.
   * @return A list of methods in the_class to test.
   */
  /*@ ensures (\forall MethodInfo m; \result.contains(m); 
    @   m.isTestable() && 
    @   ((m.isInherited() && my_test_inherited_methods) || !m.isInherited()) &&
    @   ((m.isDeprecated() && my_test_deprecated_methods) || !m.isDeprecated()));
   */
  private /*@ pure non_null @*/ Set<MethodInfo> getMethodsToTest
  (final /*@ non_null @*/ ClassInfo the_class) {
    final Set<MethodInfo> methods = new HashSet<MethodInfo>();
    for (MethodInfo m : the_class.getTestableMethods()) {
      if (m.getProtectionLevel().weakerThanOrEqualTo(my_config.getProtectionLevel()) &&
          (my_config.isInheritedSet() || !m.isInherited()) &&
          (my_config.isDeprecationSet() || !m.isDeprecated())) {
        methods.add(m);
      }
    }
    return methods;
  }

  /**
   * Returns the nested classes from the given class to test based on 
   * generator settings.
   * 
   * @param the_class The class for which to find testable nested classes.
   * @return A list of nested classes in the_class to test.
   */
  private /*@ pure non_null @*/ Set<ClassInfo> getClassesToTest
  (final /*@ non_null @*/ ClassInfo the_class) {
    final Set<ClassInfo> classes = new HashSet<ClassInfo>();
    for (ClassInfo c : the_class.getNestedClasses()) {
      if (!c.isInner() && 
          c.getProtectionLevel().weakerThanOrEqualTo(my_config.getProtectionLevel())) {
        classes.add(c);
      }
    }
    return classes;
  }
  
  /**
   * Returns the basic types present in the parameters of the given methods.
   * 
   * @param the_methods The methods for which to find parameter basic types.
   * @return A list of basic types.
   */
  private /*@ pure non_null @*/ Set<TypeInfo> getUniqueParameterTypes
  (final /*@ non_null @*/ Set<MethodInfo> the_methods) {
    final SortedSet<TypeInfo> classes = new TreeSet<TypeInfo>();
    for (MethodInfo m : the_methods) {
      for (ParameterInfo p : m.getParameters()) {
        classes.add(p.getType());
        // make sure we add component types of arrays too
        TypeInfo t = p.getType();
        while (t.getArrayComponent() != null) {
          t = new TypeInfo(t.getArrayComponent());
          classes.add(t);
        }
      }
    }
    return classes;
  }
  
  /**
   * Generates a list of the publicly-visible child classes of the class
   * represented by the specified ClassInfo.
   * 
   * @param the_class The ClassInfo for which to find the children.
   * @return The child classes, in the form "fully.qualified.Name.class".
   */
  private SortedSet<String> getChildrenFromClassInfo(final ClassInfo the_class) {
    final SortedSet<String> result = new TreeSet<String>();
    final SortedSet<ClassInfo> raw_children = 
      InfoFactory.getConcreteChildren(the_class);
    
    // remove non-public children so we don't try to generate them
    final Iterator<ClassInfo> ci = raw_children.iterator();
    while (ci.hasNext()) {
      if (ci.next().getProtectionLevel() != ProtectionLevel.PUBLIC) {
        ci.remove();
      }
    }
    
    for (ClassInfo c : raw_children) {
      result.add(c.getFullyQualifiedName() + ".class");
    }
    
    return result;
  }
  
  /**
   * Checks the specified set of class literal names to see if they are 
   * child classes of the specified class, and returns only the ones that are.
   * 
   * @param the_class The class.
   * @param the_literals The literals.
   * @return the subset of the_literals that are child classes of the_class.
   */
  private SortedSet<String> checkChildLiterals(final ClassInfo the_class, 
                                               final SortedSet<String> the_literals) {
    final SortedSet<String> result = new TreeSet<String>();
    Class<?> parent = null;
    try {
      parent = Class.forName(the_class.getFullyQualifiedName());
    } catch (final ClassNotFoundException e) {
      // this should never happen if the class compiled... if it does,
      // we simply cannot proceed so we just ignore the problem
    }
    if (parent != null) {
      for (Object o : the_literals) {
        try {
          // class literals end in ".class" so we need to peel that off
          final String child_fq_name = 
            o.toString().substring(0, o.toString().lastIndexOf('.'));
          final Class<?> child = Class.forName(child_fq_name);
          if (parent.isAssignableFrom(child)) {
            result.add(o.toString());
          }
        } catch (final ClassNotFoundException e) {
          // this also should never happen if the class compiled... if
          // it does, we just ignore it
        }
      }
    }
    return result;
  }
}

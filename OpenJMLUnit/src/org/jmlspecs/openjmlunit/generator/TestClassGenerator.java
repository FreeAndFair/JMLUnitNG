/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @author Jonathan Hogins
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

import java.io.FileReader;
import java.io.IOException;
import java.io.Writer;
import java.text.DateFormat;
import java.util.Calendar;

import org.antlr.stringtemplate.StringTemplate;
import org.antlr.stringtemplate.StringTemplateGroup;

/**
 * Generator for classes that contain unit tests.
 * 
 * @author Jonathan Hogins
 * @version "April 2010"
 */
public class TestClassGenerator {
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
   * The max protection level for which to generate tests.
   */
  private ProtectionLevel my_level;
  /**
   * Do I test inherited methods?
   */
  private boolean my_test_inherited_methods;
  /**
   * Do I test deprecated methods?
   */
  private boolean my_test_deprecated_methods;

  /**
   * Create a new TestClassGenerator with the default options.
   */
  public TestClassGenerator() {
    this(DEF_PROTECTION_LEVEL, DEF_TEST_INHERITED_METHODS, DEF_TEST_DEPRECATED_METHODS);
  }

  /**
   * Create a new TestClassGenerator with the given options.
   * 
   * @param the_protection_level The maximum protection level for which to
   *          generate method tests.
   * @param the_test_inherited_methods Do I test inherited methods?
   * @param the_test_deprecated_methods Do I test deprecated methods?
   */
  public TestClassGenerator(final ProtectionLevel the_protection_level,
                            final boolean the_test_inherited_methods,
                            final boolean the_test_deprecated_methods) {
    my_level = the_protection_level;
    my_test_inherited_methods = the_test_inherited_methods;
    my_test_deprecated_methods = the_test_deprecated_methods;
  }

  /**
   * Generate tests for methods of protection level at most the_level. Must not
   * be NO_LEVEL.
   * 
   * @param the_protection_level The max protection level of methods for which
   *          to generate tests.
   */
  // @ requires !the_protection_level.equals(ProtectionLevel.NO_LEVEL);
  public void setMaxProtectionLevel(final ProtectionLevel the_protection_level) {
    my_level = the_protection_level;
  }

  /**
   * Returns the maximum protection level of methods for which tests will be
   * generated.
   * 
   * @return The maximum method protection level for which tests will be
   *         generated.
   */
  public ProtectionLevel getMaxProtectionLevel() {
    return my_level;
  }

  // "Generate tests for inherited methods!",
  /**
   * Sets whether or not tests will be generated for inherited methods.
   * 
   * @param the_test_inherited_methods If true, inherited methods will be
   *          tested.
   */
  public void setTestInheritedMethods(final boolean the_test_inherited_methods) {
    my_test_inherited_methods = the_test_inherited_methods;
  }

  /**
   * Returns whether or not tests will be generated for inherited methods.
   * 
   * @return True if tests will be generated for inherited methods.
   */
  public boolean getTestInheritedMethods() {
    return my_test_inherited_methods;
  }

  // "Generate tests for deprecated methods!",
  /**
   * Sets whether or not tests will be generated for deprecated methods.
   * 
   * @param the_test_deprecated_methods If true, deprecated methods will be
   *          tested.
   */
  public void setTestDeprecatedMethods(final boolean the_test_deprecated_methods) {
    my_test_deprecated_methods = the_test_deprecated_methods;
  }

  /**
   * Returns whether or not tests will be generated for deprecated methods.
   * 
   * @return True if tests will be generated for deprecated methods.
   */
  public boolean getTestDeprecatedMethods() {
    return my_test_deprecated_methods;
  }

  /**
   * Generates a test class for the_class and writes it to the_writer.
   * 
   * @param the_class The ClassInfo for which to generate a test class.
   * @param the_writer The writer for which to output class data.
   * @throws IOException Thrown if an IOException occurs while writing to
   *           the_writer.
   */
  public void generateTestClass(final ClassInfo the_class, final Writer the_writer)
    throws IOException {
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = 
      StringTemplateGroup.loadGroup("test_class_java");
    final StringTemplate t = group.getInstanceOf("main");
    t.setAttribute("class", the_class);
    t.setAttribute("date", 
                   DateFormat.getDateInstance().format(Calendar.getInstance().getTime()));
    the_writer.write(t.toString());
  }
}

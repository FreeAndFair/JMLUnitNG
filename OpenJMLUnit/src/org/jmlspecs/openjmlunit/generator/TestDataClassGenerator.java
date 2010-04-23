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

import java.io.IOException;
import java.io.Writer;

/**
 * Generator for classes that contain unit test data.
 * 
 * @author Jonathan Hogins
 * @version "April 2010"
 */
public class TestDataClassGenerator extends TestClassGenerator {
  /**
   * Do test data classes use reflection by default?
   */
  public static final boolean DEF_USE_REFLECTION = true;

  /**
   * Do I use reflection?
   */
  private boolean my_use_reflection;

  /**
   * Create a new TestClassGenerator with the default options.
   */
  public TestDataClassGenerator() {
    this(DEF_PROTECTION_LEVEL, DEF_TEST_INHERITED_METHODS, DEF_TEST_DEPRECATED_METHODS,
         DEF_USE_REFLECTION);
  }

  /**
   * Create a new TestClassGenerator with the given options.
   * 
   * @param the_protection_level The maximum protection level for which to
   *          generate method tests.
   * @param the_test_inherited_methods Do I test inherited methods?
   * @param the_test_deprecated_methods Do I test deprecated methods?
   * @param the_use_reflection Do I use reflection to resolve classes?
   */
  public TestDataClassGenerator(final ProtectionLevel the_protection_level,
                                final boolean the_test_inherited_methods,
                                final boolean the_test_deprecated_methods,
                                final boolean the_use_reflection) {
    super(DEF_PROTECTION_LEVEL, DEF_TEST_INHERITED_METHODS, DEF_TEST_DEPRECATED_METHODS);
    my_use_reflection = the_use_reflection;
  }

  /**
   * Sets whether or not this generator will use reflection in the generated
   * test classes.
   * 
   * @param the_use_reflection If true, reflection will be used to generate test
   *          classes.
   */
  public void setUseReflection(final boolean the_use_reflection) {
    my_use_reflection = the_use_reflection;
  }

  /**
   * Returns true if the generated classes will use reflection. False if not.
   * 
   * @return True if the generated classes will use reflection. False if not.
   */
  public boolean getUseReflection() {
    return my_use_reflection;
  }

  /**
   * Generates a test data class for the_class and writes it to the_writer.
   * 
   * @param the_class The ClassInfo for which to generate a test class.
   * @param the_writer The writer for which to output class data.
   * @throws IOException Thrown if an IOException occurs while writing to
   *           the_writer.
   */
  public void generateTestDataClass(final ClassInfo the_class, final Writer the_writer)
    throws IOException {
    
  }
  // "Generate test data of classes the_gen_classes for parameters of class the_param_class!",
}

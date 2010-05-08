
package org.jmlspecs.openjmlunit.generator;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.Writer;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

/**
 * This class generates the XML file to run the Test using TestNG framework.
 * Based on the class with the same name in JMLUnitNG by Rinkesh Nagmoti.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public final class XMLGenerator {
  /**
   * The filename of the xml properties file.
   */
  private static final String PROPS_FILENAME = "res/xml.properties";
  /**
   * The number of spaces for indents.
   */
  private static final int INDENT_SIZE = 2;
  /**
   * The string to use for indents.
   */
  private static final char INDENT_CHARACTER = ' ';
  /**
   * The constants for XML generation.
   */
  private static ResourceBundle prop_bundle;

  /**
   * Private constructor to prevent instantiation.
   */
  private XMLGenerator() {
  }

  /**
   * Generates and writes a TestNG configuration XML file for the given class to
   * the given writer.
   * 
   * @param the_class The class for which to create a configuration xml.
   * @param the_writer The writer for which to send the generated xml file.
   * @throws IOException throws exception if failed to load xml properties or
   *           failed to write to writer.
   */
  public static void generateXML(final ClassInfo the_class,
                                 final Writer the_writer) throws IOException {
    final List<ClassInfo> list = new LinkedList<ClassInfo>();
    list.add(the_class);
    generateXML(list, the_writer);
  }

  /**
   * Generates and writes a TestNG configuration XML file for the given classes to
   * the given writer.
   * 
   * @param the_classes The classes for which to create a configuration xml.
   * @param the_writer The writer for which to send the generated xml file.
   * @throws IOException throws exception if failed to load xml properties or
   *           failed to write to writer.
   */
  public static void generateXML(final Collection<ClassInfo> the_classes,
                                 final Writer the_writer) throws IOException {
    if (prop_bundle == null) {
      prop_bundle = new PropertyResourceBundle(new FileInputStream(PROPS_FILENAME));
    }
    final SourceWriter swrite =
        new SourceWriter(the_writer, prop_bundle, INDENT_SIZE, INDENT_CHARACTER);
    swrite.writeLine(getProp("HEADER"));
    swrite.writeLine(getProp("SUITE_OPEN") + " " + getProp("DEF_SUITE_ATTRIBS") +
                     getProp("XML_B_CLOSE"));
    swrite.incrementIndentLevel();
    swrite.writeLine(getProp("TEST_OPEN") + " name= \"TestNG test\" junit=\"false\"" +
                     getProp("XML_B_CLOSE"));
    swrite.incrementIndentLevel();
    swrite.writeLine(getProp("CLSS_OPEN") + getProp("XML_B_CLOSE"));
    swrite.incrementIndentLevel();
    for (TypeInfo cls : the_classes) {
      writeClass(cls, swrite);
    }
    swrite.decrementIndentLevel();
    swrite.writeLine(getProp("CLSS_CLOSE"));
    swrite.decrementIndentLevel();
    swrite.writeLine(getProp("TEST_CLOSE"));
    swrite.decrementIndentLevel();
    swrite.writeLine(getProp("SUITE_CLOSE"));
  }

  /**
   * Writes the testing XML to for the given class.
   * 
   * @param the_class The class for which to generate xml.
   * @param the_writer The writer to print to.
   * @throws IOException throws exception if failed to load xml properties or
   *           failed to write to writer.
   */
  private static void writeClass(final TypeInfo the_class, final SourceWriter the_writer)
    throws IOException {
    the_writer.writeLine(getProp("CLS_OPEN") + " name=\"" + the_class.getShortName() + "\"" +
                         getProp("XML_B_CLOSE"));
  }

  /**
   * A convenience method for returning properties from prop_bundle.
   * 
   * @param the_prop The property key.
   * @return The value of the given property
   */
  private static String getProp(final String the_prop) {
    return prop_bundle.getString(the_prop);
  }
}

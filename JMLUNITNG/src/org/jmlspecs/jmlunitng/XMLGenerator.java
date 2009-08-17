package org.jmlspecs.jmlunitng;

import java.io.IOException;

import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JTypeDeclarationType;

/**
 *  This class generates the XML file to run the Test using TestNG framework.
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class XMLGenerator implements Constants
{
  /**
   * This is the file writer object to write the XML file.
   */
  private final transient Writer my_writer;
 /**
  * This is the JTypeDeclarationType object.
  */
  private final transient JTypeDeclarationType my_decl;
  /**
   * This is the JCompilationUnit object.
   */
  private final transient JCompilationUnit my_cunit;
  /**
   * Constructs the XMLGenerator object.
   * @param the_decl JTypeDeclarationType object.
   * @param the_cunit JCompilationUnit object.
   * @throws IOException throws exception if failed to initialize my_writer.
   */
  public XMLGenerator(final JTypeDeclarationType the_decl, 
                      final JCompilationUnit the_cunit) throws IOException
  {
    
    my_writer = new Writer("C:\\" + the_decl.ident() + XML_POSTFIX);
    my_decl = the_decl;
    my_cunit = the_cunit;
  }
/**
 * This method creates an XML file.
 */
  public void createXML()
  {
    printDocType();
    printXML();
  }
  /**
   * This method prints the DocType in XML file.
   */
  private void printDocType()
  {
    my_writer.print("<!DOCTYPE suite SYSTEM \"http://testng.org/testng-1.0.dtd\">");
  }
  /**
   * This is the method to print remaining XML document.
   */
  private void printXML()
  {
    my_writer.print(SUITE_OPEN + " skipfailedinvocationCounts=\"false\" " +
       "verbose=\"1\" name=\"" + my_decl.ident() + " Suite\"" + 
       " junit=\"false\" annotations=\"JDK\"" + XML_B_CLOSE);
    
    my_writer.indent(LEVEL1);
    my_writer.print(TEST_OPEN + " name= \"" + my_decl.ident() +
                    " test\"" + " junit=\"false\"" + XML_B_CLOSE);
    
    my_writer.indent(LEVEL2);
    my_writer.print(CLSS_OPEN + XML_B_CLOSE);
    my_writer.indent(LEVEL3);
    my_writer.print(CLS_OPEN + " name=\"" +
                    my_cunit.packageNameAsString().replaceAll("/", "") +
                    "." + my_decl.ident() + T_C_POSTFIX + "\"" + CLS_CLOSE);
    my_writer.indent(LEVEL2);
    my_writer.print(CLSS_CLOSE);
    
    
    my_writer.indent(LEVEL1);
    my_writer.print(TEST_CLOSE);
    my_writer.print(SUITE_CLOSE);
    
  }
}

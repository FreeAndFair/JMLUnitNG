
package org.jmlspecs.jmlunitng;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Iterator;
import org.jmlspecs.jmlunit.JntOptions;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MjcCommonOptions;
import org.multijava.mjc.ParsingController.ConfigurationException;
import org.testng.log4testng.Logger;

import antlr.RecognitionException;
import antlr.TokenStreamException;

/**
 * This class creates the test classes after receiving command from command
 * line.
 * 
 * @author Rinkesh Nagmoti.
 * @version 1.0 Some of the code is taken from MultiJava open source project.
 */
public class MainClass
{
  /**
   * MjcComminOptions instance to parse the given file.
   */
  protected final transient MjcCommonOptions my_options;

  /**
   * Constructs the MainClass object.
   */
  public MainClass()
  {
    my_options = new JntOptions("jmlunitng");
  }
  
  /**
   * This method is the entry point for the tool.
   * 
   * @param the_args This is the argument to be passed to main method.
   * @throws FileNotFoundException  exception if unable to find the file.
   */
  public static void main(final String[]/* @ not null @ */the_args)
    throws FileNotFoundException
  {
    final Logger my_logger = Logger.getLogger(org.jmlspecs.jmlunitng.MainClass.class);
    final MainClass my_Main = new MainClass();
    JCompilationUnit j_type = null;
    MJClassParser parser;
    final File parsedArguments = new File(the_args[0]);
    try
    {
      
      parser = new MJClassParser(parsedArguments, my_Main.my_options);
      j_type = (JCompilationUnit) parser.parse();

    }
    catch (final TokenStreamException e)
    {
      my_logger.error("TokenStreamException " + e.getMessage());
      
    } 
    catch (final RecognitionException e)
    {
      my_logger.error("RecognitionException " + e.getMessage());
    } 
    catch (final ConfigurationException e)
    {
      my_logger.error("ConfigurationException " + e.getMessage());
    }
   

    final JTypeDeclarationType[] decl = j_type.typeDeclarations();

    final TestClassGenerator testgen = new 
    TestClassGenerator("c:\\" + decl[0].ident() + "_JMLUNITNG_Test.java", decl[0], j_type);
    testgen.createTest(decl[0], j_type, my_Main.getMethodIterator(decl[0]));

    final TestDataClassGenerator testDataGen = new 
    TestDataClassGenerator("c:" + "\\" + decl[0].ident() + "_JMLUNITNG_Test_Data.java",
                           decl[0], j_type);
    testDataGen.createTestDataClass(decl[0], j_type, my_Main.getMethodIterator(decl[0]));
  }

  /**
   * Returns the Method iterator.
   * @param the_decl This is JTypeDeclarationType object to be passed as argument.
   * @return Iterator.
   */
  protected Iterator<JTypeDeclarationType> getMethodIterator
  (final JTypeDeclarationType the_decl)
  {
    return the_decl.methods().iterator();
  }
}

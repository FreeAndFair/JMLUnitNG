
package org.jmlspecs.jmlunitng;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Iterator;
import org.jmlspecs.jmlunit.JntOptions;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MjcCommonOptions;
import org.multijava.mjc.ParsingController.ConfigurationException;
import org.multijava.util.Utils;
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
public class MainClass implements Constants
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
    final JTypeDeclarationType[] declarations = new JTypeDeclarationType[the_args.length]; 
    final JCompilationUnit[] jcunits = new JCompilationUnit[the_args.length];
    JCompilationUnit j_type = null;
    MJClassParser parser;
    String path = null;

    for (int i = 0; i < the_args.length; i++)
    {
      final File parsedArguments = new File(the_args[i]);
      try
      {
        
        parser = new MJClassParser(parsedArguments, my_Main.my_options);
        
        j_type = (JCompilationUnit) parser.parse();
        jcunits[i] = j_type;
        path = Utils.getFilePath(parsedArguments);
        final String location = path.replace(".java", "");
        path = location.replace("\\", "\\\\");
//        final StringBuilder loc = new StringBuilder();
//        for (int count = 0; count < location.length - 1; count++)
//        {
//          loc.append(location[count]);
//          
//          if (count == 0)
//          {
//            loc.append("\\\\");
//          }
//          else
//          {
//            loc.append("\\");  
//          }
//        }
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
      declarations[i] = decl[0];
      final TestClassGenerator testgen = new 
      TestClassGenerator(path  + T_C_FILE_POSTFIX, decl[0], j_type);
      testgen.createTest(decl[0], j_type, my_Main.getMethodIterator(decl[0]));
  
      final TestDataClassGenerator testDataGen = new 
      TestDataClassGenerator(path  + T_D_FILE_POSTFIX,
                             decl[0], j_type);
      testDataGen.createTestDataClass(decl[0], j_type, my_Main.getMethodIterator(decl[0]));
      
    }
    XMLGenerator xmlgen = null;
   
    try
    {
      xmlgen = new XMLGenerator(declarations, jcunits);
      xmlgen.createXML();
    }
    catch (final IOException the_exp)
    {
      my_logger.error("IOException " + the_exp.getMessage());
    }
    
     
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

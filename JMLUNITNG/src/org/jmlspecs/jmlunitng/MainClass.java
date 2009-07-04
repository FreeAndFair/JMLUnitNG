package org.jmlspecs.jmlunitng;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.List;

import javax.print.attribute.standard.Destination;

import org.multijava.mjc.CMethod;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JavadocLexer;
import org.multijava.mjc.Main;
import org.multijava.mjc.MjcLexer;
import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.MjcOptions;
import org.multijava.mjc.MjcParser;
import org.multijava.mjc.ParsingController;
import org.multijava.mjc.ParsingController.ConfigurationException;
import org.multijava.mjc.ParsingController.KeyException;
import org.multijava.util.FormattedException;
import org.multijava.util.compiler.CompilerMessages;

import com.sun.org.apache.xml.internal.utils.URI;

import antlr.RecognitionException;
import antlr.TokenStreamException;


/**
 * This class creates the test classes after receiving command
 * from command line.
 * @author Rinkesh Nagmoti. 
 * @version 1.0
 * Some of the code is taken from MultiJava open source project.
 */
public class MainClass extends Main
{
  private  MjcOptions options;
  
 
  /**
   * This method is the entry point for the tool.
   * @param the_args 
   */
  public static void main(final String[]/*@ not null @*/ the_args)
  {
    
    final MainClass my_Main = new MainClass();
    JCompilationUnitType jType = null;
    final File parsedArguments = new File(the_args[0]);
    try{
      my_Main.options = new MjcOptions(); 
      MJClassParser parser = new MJClassParser(parsedArguments, my_Main.options);
      jType = parser.parse();
    }
    catch (Exception e)
    {
      e.printStackTrace();
    }
    URI uri = new URI();
    
    
    final JTypeDeclarationType[] decl = jType.typeDeclarations();
   
 
    final String file = "C:\test.java";
    
    final TestClassGenerator my_testClass = new TestClassGenerator(file);
    my_testClass.createTest(decl[0], jType);

  }

}

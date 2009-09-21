
package org.jmlspecs.jmlunitng;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

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
   * @throws InvalidOptionPropertyValueException if invalid option is specified.
   * @throws InvalidOptionValueException  if invalid option value is specified.
   * @throws AutomatonException  if AutomationException occurs.
   */
  public static void main(final String[]/* @ not null @ */the_args)
    throws FileNotFoundException, InvalidOptionPropertyValueException, 
    AutomatonException, InvalidOptionValueException
  {
    
    final CmdOptionsParser jparser = new CmdOptionsParser();
    jparser.parse(the_args);
    final CmdOptionsOptionsInterface my_opt = jparser.getOptionStore();
    List<File> file_list = new ArrayList<File>();
    
    if (my_opt.isHelpSet())
    {
      printHelp();
    }
    if (my_opt.isListSet() || my_opt.isPackageSet())
    {
      if (my_opt.isListSet())
      {
        file_list = my_opt.getList();
      }
      if (my_opt.isPackageSet())
      {
        final List<File> all_packages = my_opt.getPackage();
        for (int cnt = 0; cnt < all_packages.size(); cnt++)
        {
          
          final File[] all_packed_files = all_packages.get(cnt).listFiles();
          for (int k = 0; k < all_packed_files.length; k++)
          {
            if (all_packed_files[k].getPath().endsWith(".java"))
            {
              file_list.add(all_packed_files[k]);
            }
          }
        }
      }
      
    
    }
    else
    {
      System.out.println("Enter valid file names or package names.");
      System.exit(1);
    }
    
    final Logger my_logger = Logger.getLogger(org.jmlspecs.jmlunitng.MainClass.class);
    final MainClass my_Main = new MainClass();
    final JTypeDeclarationType[] declarations = new JTypeDeclarationType[file_list.size()]; 
    final JCompilationUnit[] jcunits = new JCompilationUnit[file_list.size()];
    JCompilationUnit j_type = null;
    MJClassParser parser;
    String path = null;
    
   
    for (int i = 0; i < file_list.size(); i++)
    {
      //final File parsedArguments = new File(the_args[i]);
      
      try
      {
        
        parser = new MJClassParser(file_list.get(i), my_Main.my_options);
        boolean universes, deprication, safemath = false;
        String universesx;
        if(my_opt.isUniversesxSet())
        {
         universesx = my_opt.getUniversesx(); 
        }
        else
        {
          universesx = null;
        }
        
        j_type = (JCompilationUnit) parser.parse(my_opt.isUniversesSet(), my_opt.isDepricationSet(), my_opt.isSafeMathSet(), my_opt.isVerboseSet(), universesx);
        jcunits[i] = j_type;
        if (my_opt.isDestinationSet())
        {
          final String dest = my_opt.getDestination();
          if (dest.endsWith("\\"))
          {
            path = dest + file_list.get(i).getName().replaceAll(".java", "");
          }
          else
          {
            path = dest + "\\" + file_list.get(i).getName().replaceAll(".java", "");
          }
        }
        else
        {
          path = Utils.getFilePath(file_list.get(i));
          final String location = path.replace(".java", "");
          path = location.replace("\\", "\\\\");
        }
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
   
    if (file_list.size() > 0)
    {
      try
      {
        if (my_opt.isDestinationSet())
        {
          
          if (my_opt.getDestination().endsWith("\\"))
          {
            path = my_opt.getDestination();
          }
          else
          {
            path = my_opt.getDestination()+ "\\";
          }
        }
        else
        {
          path = file_list.get(0).getPath();
          final int index = path.lastIndexOf("\\");
          final String xmlpath = path.substring(0, index);
          path = xmlpath + "\\";
        }
        xmlgen = new XMLGenerator(declarations, jcunits, path);
        xmlgen.createXML();
      }
      catch (final IOException the_exp)
      {
        my_logger.error("IOException " + the_exp.getMessage());
      }
    }
     
  }

  /**
   * This method prints the options in help menu.
   */
  protected static void printHelp()
  {
    System.out.println("-d, --dest : To specify the oputput directory for generated files.");
    System.out.println("-f, --files : To specify the files for testing with jmluning.");
    System.out.println("-h, --help : To see command line options.");
    System.out.println("-p, --package : To specify the files for testing" +
                         " with jmluning.");
    System.out.println("-u, --universes : Enable universe type modifiers and full" +
                         " type checking.");
    System.out.println("-dep, --deprication : Test for Depricated members.");
    System.out.println("-s, --safemath : Report Integral Arithmatic Overflow.");
    System.out.println("-v, --verbose : Display verbose information during" +
                                      " compilation.");
    System.out.println("-E : Universe type system.");
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


package org.jmlspecs.jmlunitng;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Iterator;
import org.jmlspecs.jmlunit.JntOptions;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MjcCommonOptions;

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
  protected MjcCommonOptions options;

  /**
   * This method is the entry point for the tool.
   * 
   * @param the_args
   * @throws FileNotFoundException
   */
  public static void main(final String[]/* @ not null @ */the_args)
      throws FileNotFoundException
  {

    final MainClass my_Main = new MainClass();
    JCompilationUnit jType = null;
    MJClassParser parser;
    final File parsedArguments = new File(the_args[0]);
    try
    {
      my_Main.options = new JntOptions("jmlunitng");
      parser = new MJClassParser(parsedArguments, my_Main.options);
      jType = (JCompilationUnit) parser.parse();

    }
    catch (Exception e)
    {
      e.printStackTrace();
    }

    final JTypeDeclarationType[] decl = jType.typeDeclarations();

    TestClassGenerator testgen = new TestClassGenerator("c:\\Addition_JMLUNITNG_Test.java");
    testgen.createTest(decl[0], jType, my_Main.getMethodIterator(decl[0]));

    TestDataClassGenerator testDataGen = new TestDataClassGenerator("c:\\Addition_JMLUNITNG_Test_Data.java");
    testDataGen.createTestDataClass(decl[0], jType, my_Main.getMethodIterator(decl[0]));
  }

  /**
   * Returns the Method iterator.
   * 
   * @return Iterator.
   */
  protected Iterator getMethodIterator(JTypeDeclarationType the_decl)
  {
    return the_decl.methods().iterator();
  }
}

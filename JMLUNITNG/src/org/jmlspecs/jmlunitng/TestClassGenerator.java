
package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.util.Date;
import java.util.Iterator;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JConstructorDeclaration;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JPackageImportType;
import org.multijava.mjc.JTypeDeclarationType;
import org.testng.TestNG;

import Test.Multiply_JMLUNITNG_Test;

/**
 * Generates the JMLUNITNG_Test class by JMLUNITNG framework. The generated
 * class runs unit tests for the class to be tested using JMLUNITNG testing
 * framework.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class TestClassGenerator implements Constants
{

  /**
   * Represents the class name for the Test class to be generated.
   */
  protected final transient/* @ spec_public @ */String my_class_name;

  /** Writer class object to print the Test Class. */
  protected final transient/* @ spec_public @ */Writer my_writer;

  /** String representing the file name and location for Test Class. */
  protected final transient/* @ spec_public @ */String my_file;

  /**
   * JTypeDeclarationType object which holds information about the class for
   * which the test is to be conducted.
   */
  protected final transient/* @ spec_public @ */JTypeDeclarationType my_decl_type;

  /**
   * This array represents the list of imported packages.
   */
  protected final transient/* @ spec_public @ */JPackageImportType[] my_pkgs;

  /**
   * This is the list of all the methods the class to be tested contains.
   */
  // protected List<Object> my_methods;

  /**
   * Constructs the TestClassGenerator Object.
   * 
   * @param the_file The file to write the generated class to.
   * @param the_decl the JTypeDeclarationType object.
   * @param the_cunit_type JCompilationUnit object.
   * @throws FileNotFoundException  Exception if unable to find the specified file.
   */
  public TestClassGenerator(final/* @ non_null @ */String the_file,
                            final JTypeDeclarationType the_decl,
                            final JCompilationUnit the_cunit_type) throws FileNotFoundException
  {
    this.my_pkgs = the_cunit_type.importedPackages();
    this.my_decl_type = the_decl;
    this.my_class_name = the_decl.ident() + T_C_POSTFIX;
    this.my_file = the_file;
    my_writer = new Writer(the_file);
    
  }

  /**
   * Calls other methods to generate the Test Class.
   * 
   * @param the_decl JTypeDeclarationType object.
   * @param the_cunit_type JCompilationUnit object.
   * @param the_iter Iterator object.
   */
  public void createTest(final JTypeDeclarationType the_decl,
                         final JCompilationUnit the_cunit_type,
                         final Iterator<JTypeDeclarationType> the_iter)
  {

    printHeaderImportandJavadoc(the_decl);
    printDataMembers();
    printConstructor();
    printMainMethod();
    createTestMethods(the_iter, the_decl);
    printClassEnd();
  }

  /**
   * Prints Class header import statements and class Javadoc comment.
   * 
   * @param the_decl JTypeDeclarationType object.
   */
  private void printHeaderImportandJavadoc(final JTypeDeclarationType the_decl)
  {

   

    my_writer.print("//This class is generated by JMLUNITNG on " + new Date());
    my_writer.newLine(LEVEL1);
    for (int j = 0; j < my_pkgs.length; j++)
    {
      my_writer.print("import " + my_pkgs[j].getName().replace('/', '.') + ".*" + SM_COLN);
    }

    my_writer.print("import org.multijava.*" + SM_COLN);
    my_writer.print("import org.testng.*" + SM_COLN);
    my_writer.print("import org.jmlspecs.*" + SM_COLN);
    my_writer.print("import org.testng.annotations.Test;");
    my_writer.print("import org.jmlspecs.jmlunitng.PreconditionSkipException;");
    my_writer.print("import org.jmlspecs.jmlunitng.TestListener;");
    my_writer.print("import org.testng.TestNG;");
    my_writer.newLine(LEVEL1);
    my_writer.print(JDOC_ST + " This class is the test oracle generated by JMLUNITNG");
    my_writer.print(" * testing framework for class " + the_decl.ident() + PERIOD);
    my_writer.print(" * @version 1.0");
    my_writer.print(" * @author Rinkesh Nagmoti.");
    my_writer.print(JDOC_END);
    my_writer.print("public class " + my_class_name + " extends " + my_class_name + "_Data");
    my_writer.print(BLK_ST);
  }

  /** Prints the constructor of the Test class to be generated. */
  private void printConstructor()
  {
    my_writer.indent(LEVEL1);
    my_writer.print(JDOC_ST);
    my_writer.indent(LEVEL1);
    my_writer.print(" * Constructs the class object.");
    my_writer.indent(LEVEL1);
    my_writer.print(JDOC_END);
    my_writer.indent(LEVEL1);
    my_writer.print(PUBLIC + SPACE + my_class_name + BKTS);
    my_writer.indent(LEVEL1);
    my_writer.print(BLK_ST);
    my_writer.indent(LEVEL1);
    my_writer.print(BLK_END);
    my_writer.newLine(LEVEL1);
  }

  /**
   * Creates and prints the methods generated for Testing the methods.
   * 
   * @param the_decl JTypeDeclarationType object.
   * @param the_method_iter Iterator object.
   */
  private void createTestMethods(final Iterator<JTypeDeclarationType> the_method_iter,
                                 final JTypeDeclarationType the_decl)
  {
    while (the_method_iter.hasNext())
    {
      final Object obj = the_method_iter.next();
      if (obj instanceof JConstructorDeclaration)
      {
        final JConstructorDeclaration construct = (JConstructorDeclaration) obj;
        final String name = generateMethodName(obj);
        printMethodJavaDoc(obj, name);
        my_writer.indent(LEVEL1);
        my_writer.printOnLine(PUBLIC + SPACE + "void " + name + "(" + "final " + 
                              the_decl.ident() + SPACE + "the_obj");
        for (int i = 0; i < construct.parameters().length; i++)
        {
          my_writer.printOnLine("," + " final " + construct.parameters()[i].typeToString() + 
                                SPACE + PARAM_ST + construct.parameters()[i].ident());
        }
        my_writer.printOnLine(BKT_END);
        my_writer.printOnLine(" \n");
        my_writer.indent(LEVEL1);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL2);
        my_writer.print(TRY);
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL3);
        my_writer.printOnLine("new " + construct.ident() + BKT_ST);
        for (int i = 0; i < construct.parameters().length; i++)
        {
          my_writer.printOnLine(PARAM_ST + construct.parameters()[i].ident());
          if (i != construct.parameters().length - 1)
          {
            my_writer.printOnLine(COMMA + SPACE);
          }
        }
        my_writer.printOnLine(BKT_END + SM_COLN);
        my_writer.printOnLine("\n");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_END);
        my_writer.indent(LEVEL2);
        my_writer.print(CATCH + SPACE + 
          "(final" + " org.jmlspecs.jmlrac.runtime.JMLEntryPreconditionError the_exp)");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL3);
        my_writer.print("throw new" + " PreconditionSkipException(the_exp.getMessage())" +
                        SM_COLN);
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_END);
        my_writer.indent(LEVEL2);
        my_writer.print(CATCH + SPACE + 
          " (final org.jmlspecs.jmlrac.runtime.JMLInternalPreconditionError" +
          " the_exp)");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL3);
        my_writer.print("throw " + "new PreconditionSkipException(the_exp.getMessage());");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_END);
        my_writer.indent(LEVEL1);
        my_writer.print(BLK_END);
        my_writer.newLine(ONE);
      }
      else if (obj instanceof JMethodDeclaration)
      {
        final String name = generateMethodName(obj);
        printMethodJavaDoc(obj, name);
        final JMethodDeclaration method = (JMethodDeclaration) obj;
        my_writer.indent(LEVEL1);
        my_writer.printOnLine("public void " + name + "(final " +
                              the_decl.ident() + " the_obj");
        for (int i = 0; i < method.parameters().length; i++)
        {
          my_writer.printOnLine(", final " + method.parameters()[i].typeToString() + SPACE +
                             PARAM_ST + method.parameters()[i].ident());
        }
        my_writer.printOnLine(BKT_END);
        my_writer.printOnLine("\n");
        my_writer.indent(LEVEL1);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL2);
        my_writer.print(TRY);
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL3);
        my_writer.printOnLine("the_obj." + method.ident() + BKT_ST);
        for (int i = 0; i < method.parameters().length; i++)
        {
          my_writer.printOnLine(PARAM_ST + method.parameters()[i].ident());
          if (i != method.parameters().length - 1)
          {
            my_writer.printOnLine(COMMA + SPACE);
          }
        }
        my_writer.printOnLine(BKT_END + SM_COLN);
        my_writer.printOnLine("\n");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_END);
        my_writer.indent(LEVEL2);
        my_writer.print(CATCH + SPACE + 
          "(final org.jmlspecs.jmlrac.runtime.JMLEntryPreconditionError the_exp)");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL3);
        my_writer.print("throw new PreconditionSkipException(the_exp.getMessage())" + SM_COLN);
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_END);
        my_writer.indent(LEVEL2);
        my_writer.print("catch" + 
          " (final org.jmlspecs.jmlrac.runtime.JMLInternalPreconditionError the_exp)");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_ST);
        my_writer.indent(LEVEL3);
        my_writer.print("throw new PreconditionSkipException(the_exp.getMessage());");
        my_writer.indent(LEVEL2);
        my_writer.print(BLK_END);
        my_writer.indent(LEVEL1);
        my_writer.print(BLK_END);
        my_writer.newLine(ONE);
      }
    }
  }

  /**
   * Generates the unique names for methods.
   * 
   * @param the_method the Object of type method.
   * @return String
   */
  private String generateMethodName(final Object the_method)
  {
    final StringBuilder name = new StringBuilder();
    name.append("test");
    
    if (the_method instanceof JConstructorDeclaration)
    {
      final JConstructorDeclaration construct = (JConstructorDeclaration) the_method;
      name.append(UND + construct.ident());
      final JFormalParameter[] pams = construct.parameters();
      for (int i = 0; i < pams.length; i++)
      {
        if (pams[i].typeToString().equals(STRARR))
        {
          name.append(UND + ST_ARR);
        }
        else
        {
          name.append(UND + pams[i].typeToString());
        }
      }
     

    }
    else if (the_method instanceof JMethodDeclaration)
    {
      final JMethodDeclaration method = (JMethodDeclaration) the_method;
      name.append(UND + method.ident());
      final JFormalParameter[] pams = method.parameters();
      for (int i = 0; i < pams.length; i++)
      {
        if (pams[i].typeToString().equals("String[]"))
        {
          name.append(UND + ST_ARR);
        }
        else
        {
          name.append(UND + pams[i].typeToString());
        }
      }
      
    }
    return name.toString();
      
  }

  /**
   * Prints Javadoc comment for method.
   * 
   * @param the_method An Object of type method.
   * @param the_name String name.
   */
  private void printMethodJavaDoc(final Object the_method, final String the_name)
  {

    if (the_method instanceof JConstructorDeclaration)
    {
      final JConstructorDeclaration jConstruct = (JConstructorDeclaration) the_method;
      my_writer.indent(LEVEL1);
      my_writer.print(JDOC_ST + " This method is a test " + "for Constructor " +
                      jConstruct.ident() + " from" + " the ");
      my_writer.indent(LEVEL1);
      my_writer.print(" * class" + " to  be tested.");
      my_writer.indent(LEVEL1);
      my_writer.print(" * @param" + " the_obj " + "The object to be passed.");
      for (int i = 0; i < jConstruct.parameters().length; i++)
      {
        my_writer.indent(LEVEL1);
        my_writer.print(" * @param " + "the_" + jConstruct.parameters()[i].ident() + " The " +
                     jConstruct.parameters()[i].typeToString() + " to be passed" + PERIOD);
      }
      my_writer.indent(LEVEL1);
      my_writer.print(JDOC_END);
      my_writer.indent(LEVEL1);
      my_writer.print("@Test(dataProvider" + " = \"" + the_name + "\"" + ")");

    }
    else if (the_method instanceof JMethodDeclaration)
    {
      final JMethodDeclaration method = (JMethodDeclaration) the_method;
      my_writer.indent(LEVEL1);
      my_writer.print(JDOC_ST + " This method is a test for Constructor " + method.ident() +
                   " from the ");
      my_writer.indent(LEVEL1);
      my_writer.print(" * class to  be tested.");
      my_writer.indent(LEVEL1);
      my_writer.print(" * @param the_obj The object to be passed.");
      for (int i = 0; i < method.parameters().length; i++)
      {
        my_writer.indent(LEVEL1);
        my_writer.print(" * @param the_" + method.parameters()[i].ident() + " This is the " +
                     method.parameters()[i].typeToString() + " to be passed.");
      }
      my_writer.indent(LEVEL1);
      my_writer.print(JDOC_END);
      my_writer.indent(LEVEL1);
      my_writer.print("@Test(dataProvider = \"" + the_name + "\")");
    }
  }

  /**
   * Print the main method for generated test class.
   */
  private void printMainMethod()
  {
    my_writer.indent(LEVEL1);
    my_writer.print(JDOC_ST + " This is the main method to run the test.*/");
    my_writer.indent(LEVEL1);
    my_writer.print("public static void main(String[] args)");
    my_writer.indent(LEVEL1);
    my_writer.print(BLK_ST);
    my_writer.indent(LEVEL2);
    my_writer.print("final TestNG my_test1 = new TestNG();");
    my_writer.indent(LEVEL2);
    my_writer.print("final Class[] classes " + EQUAL +  "{" + my_class_name + ".class};");
    my_writer.indent(LEVEL2);
    my_writer.print("final TestListener listener = new TestListener();");
    my_writer.indent(LEVEL2);
    my_writer.print("my_test1.setTestClasses(classes);");
    my_writer.indent(LEVEL2);
    my_writer.print("my_test1.addListener(listener);");
    my_writer.indent(LEVEL2);
    my_writer.print("my_test1.run();");
    my_writer.indent(LEVEL1);
    my_writer.print(BLK_END);
    my_writer.newLine(LEVEL1);
  }

  /**
   * This method prints the end bracket of the class.
   */
  private void printClassEnd()
  {
    my_writer.print(BLK_END);
  }

  /**
   * Print the Data members for the generated Test class.
   */
  private void printDataMembers()
  {
  // add data members to be printed here.
  }
}

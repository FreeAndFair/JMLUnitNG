
package org.jmlspecs.jmlunitng;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;

import org.jmlspecs.jmlunit.JntMessages;
import org.jmlspecs.jmlunit.JntOptions;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CompilerPassEnterable;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JTypeDeclaration;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JavadocLexer;
import org.multijava.mjc.Main;
import org.multijava.mjc.MjcCommonOptions;
import org.multijava.mjc.MjcLexer;
import org.multijava.mjc.MjcOptions;
import org.multijava.mjc.MjcParser;
import org.multijava.mjc.ParsingController;
import org.multijava.mjc.ParsingController.ConfigurationException;
import org.multijava.mjc.ParsingController.KeyException;

import antlr.RecognitionException;
import antlr.TokenStreamException;

/**
 * This class parses the given class in the AST format using MultiJava compiler.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class MJClassParser extends org.multijava.mjc.Main
{
  /**
   * MjcCommonOptions for getting the required class parsed.
   */
  protected final MjcCommonOptions my_opt;

  /**
   * File to be parsed.
   */
  protected final File my_file;

  /**
   * This is the Priority for tree processing task.
   */
  public final static int MY_PRIORITY = 500;

  /**
   * Constructs the MJClassParser object.
   * 
   * @param the_file the file to be parsed.
   * @param the_options the MjcCommonOptions object to parse the file.
   */
  public MJClassParser(final File the_file, final MjcCommonOptions the_options)
  {
    my_opt = the_options;
    my_file = the_file;
  }

  /**
   * This method parses the given class file in AST format.
   * 
   * @return JCompilationUnitType
   * @throws FileNotFoundException
   * @throws ConfigurationException
   * @throws RecognitionException
   * @throws TokenStreamException
   * @throws TokenStreamException
   */
  public JCompilationUnitType parse() throws FileNotFoundException, ConfigurationException,
      RecognitionException, TokenStreamException
  {
    BufferedReader buffer = new BufferedReader(new FileReader(my_file));
    MjcLexer mjclexer;
    JavadocLexer jdoclexer;
    MjcParser my_parser;
    JCompilationUnitType jCUnit;
    ParsingController controller;

    controller = new ParsingController(buffer, my_file);
    mjclexer =
        new MjcLexer(controller, my_opt.source().equals("1.5"), my_opt.multijava(),
                     allowUniverseKeywords, this);
    jdoclexer = new JavadocLexer(controller);

    controller.addInputStream(mjclexer, "multijava");
    controller.addInputStream(jdoclexer, "javadoc");
    controller.selectInitial("multijava");

    setAllowUniverses();

    my_parser =
        new MjcParser(this, controller.initialOutputStream(), controller, my_opt.generic(),
                      my_opt.multijava(), my_opt.relaxed(), allowUniverseKeywords,
                      parseJavadoc);

    jCUnit = my_parser.jCompilationUnit();
    return jCUnit;
  }

  /**
   * This method sets the parameters for parsing the class.
   */
  private void setAllowUniverses()
  {
    this.allowUniverseKeywords = true;
    this.allowUniverseChecks = true;
    this.allowUniversePurity = true;
    this.allowUniverseDynChecks = true;
    this.allowUniverseBytecode = true;
    this.allowUniverseAnnotations = false;
  }

}

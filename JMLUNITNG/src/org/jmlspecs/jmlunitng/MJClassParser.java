package org.jmlspecs.jmlunitng;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;

import org.multijava.mjc.JCompilationUnitType;
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
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class MJClassParser extends Main
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
   * Constructs the MJClassParser object.
   * @param the_file the file to be parsed.
   * @param the_options the MjcCommonOptions object to parse the file. 
   */
  public MJClassParser(final File the_file, final MjcCommonOptions the_options)
  {
    my_opt = the_options;
    my_file = the_file;
  }
  
  /**
   * this method parses the given class file in AST format.
   * @return JCompilationUnitType
   * @throws FileNotFoundException 
   * @throws ConfigurationException 
   * @throws TokenStreamException 
   * @throws RecognitionException 
   * @throws TokenStreamException
   */
  public JCompilationUnitType parse() throws FileNotFoundException, 
  ConfigurationException, RecognitionException, TokenStreamException
  {
    BufferedReader buffer = new BufferedReader(new FileReader(my_file));
    MjcLexer mjclexer;
    JavadocLexer jdoclexer;
    MjcParser my_parser;
    JCompilationUnitType jCUnit;
    ParsingController controller;
    options = new MjcOptions(); 
   
    controller = new ParsingController(buffer, my_file);
    mjclexer = new MjcLexer(controller, true, true, true, this);
    jdoclexer = new JavadocLexer(controller);
   
    controller.addInputStream(mjclexer, "multijava");
    controller.addInputStream(jdoclexer, "javadoc");
    controller.selectInitial("multijava");
   
    my_parser = new MjcParser(this, controller.initialOutputStream(),
                                  controller, 
                                  options.generic(),
                                  options.multijava(), 
                                  options.relaxed(),  true, true);
   
    jCUnit = my_parser.jCompilationUnit();
    return jCUnit;
  }
  
  
}

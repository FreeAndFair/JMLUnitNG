
package org.jmlspecs.jmlunitng;

/**
 * An interface for defining constants.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0 Some of the code is borrowed from open source JMLUNIT interface
 *          org.jmlspecs.jmlunit.Constants
 */
public interface Constants 
{

  /** A Dot Java extension for the file names. */
  String DOT_JAVA = ".java";
  /** Post fix for the Test Class generated by JMLUnitNG. */
  String T_C_POSTFIX = "_JML_Test";
  /** Post fix for the file name of the Test Class generated by JMLUnitNG. */
  String T_C_FILE_POSTFIX = T_C_POSTFIX + DOT_JAVA;
  /** Post fix for the TestData Class generated by JMLUnitNG. */
  String T_D_POSTFIX = "_JML_Test_Data";
  /**
   * Post fix for the file name of the TestData Class generated by JMLUnitNG.
   */
  String T_D_FILE_POSTFIX = T_D_POSTFIX + DOT_JAVA;
  /**
   * Post fix for the file name of the XML file generated by JMLUnitNG.
   */
  String XML_POSTFIX = ".xml";
  
  /** The name of the JML jmlunitng package. */
  String PKG_JMLUNITNG = "org.jmlspecs.jmlunitng.";
  /** The name of the JML jmlunitng strategies package. */
  String PKG_STRATEGIES = "org.jmlspecs.jmlunitng.strategies.";
  /** This is the start of javadoc.*/
  String JDOC_ST = "/**";
  /** This is the end of javadoc.*/
  String JDOC_END = " */";
  /** This is the Parameter start.*/
  String PARAM_ST = "the_";
  /**This is the bracket start.*/
  String BKT_ST = "(";
  /**This is the bracket end.*/
  String BKT_END = ")";
  /**This is the block start.*/
  String BLK_ST = "{";
  /**This is the block end.*/
  String BLK_END = "}";
  /**This is the square bracket start.*/
  String SQ_BCK_ST = "[";
  /**This is the square bracket end.*/
  String SQ_BCK_END = "]";
  /** This is the square brackets.*/
  String SQ_BCKTS = "[]";
  /**This is the semicolon sign.*/
  String SM_COLN = ";";

  /**This is the get method string.*/
  String GET = ".get();"; 
  /**This is the advance method string.*/
  String ADV = ".advance();"; 
  /**This is the brackets string.*/
  String BKTS = "()"; 
  /**This is the period string.*/
  String PERIOD = ".";
  /**This is the "String" string.*/
  String STR = "String";
  /**This is the "String[]" string.*/
  String STRARR = "String[]";
  /**This is the "=" string.*/
  String EQUAL = " = ";
  /**This is the " " string.*/
  String SPACE = " ";
  /**This is the "," string.*/
  String COMMA = ",";
  /**This is the "try" string.*/
  String TRY = "try";
  /**This is the "catch" string.*/
  String CATCH = "catch";
  /**This is the "\n" string.*/
  String NEWLINE = "\n";
  /**This is the "private" string.*/
  String PRIVATE = "private";
  /**This is the "public" string.*/
  String PUBLIC = "public";
  /**This is the "StringArray" string.*/
  String ST_ARR = "StringArray";
  /**This is the "my_current_objects" string.*/
  String MY_CURR_OBJS = "my_current_objects";
  /**This is the "else" string.*/
  String ELSE = "else";
  /**This is the "multijava" string.*/
  String MLTJAVA = "multijava";
   /** This is the return String.*/
  String RETURN = "return";
  /** This is the Array String.*/
  String ARR = "Array";
  /** This is the get String.*/
  String GETSTR = "get";
  /** This is the strategy String.*/
  String STRGY = "Strategy";
  /**
   * This is the underscore sign.
   */
  String UND = "_";
  /**
   * This is the constants for indentation.
   */
  int ONE = 1;
  /**
   * This is the constants for indentation.
   */
  int LEVEL1 = 2;
  /**
   * This is the constants for indentation.
   */
  int LEVEL2 = 4;
  /**
   * This is the constants for indentation.
   */
  int LEVEL3 = 6;
  /**
   * This is the constants for indentation.
   */
  int LEVEL4 = 8;
  /**
   * This is the constants for indentation.
   */
  int LEVEL5 = 10;


  /**
   * This is the XML open tag.
   */
  String XML_B_OPEN = "<";

  /**
  * This is the XML close tag.
  */
  String XML_B_CLOSE = ">";
  
  /**
  * This is the XML suite tag start.
  */
  String SUITE_OPEN = "<suite";
  /**
   * This is the XML suite tag end.
   */
  String SUITE_CLOSE = "</suite>";
  /**
   * This is the XML test tag start.
   */
  String TEST_OPEN = "<test";
   /**
    * This is the XML suite tag end.
    */
  String TEST_CLOSE = "</test>";
  /**
   * This is the XML classes tag start.
   */
  String CLSS_OPEN = "<classes";
   /**
    * This is the XML classes tag end.
    */
  String CLSS_CLOSE = "</classes>";
  /**
   * This is the XML class tag start.
   */
  String CLS_OPEN = "<class";
   /**
    * This is the XML class tag end.
    */
  String CLS_CLOSE = "/>";
}

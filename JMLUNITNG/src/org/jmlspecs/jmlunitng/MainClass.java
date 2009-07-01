package org.jmlspecs.jmlunitng;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JavadocLexer;
import org.multijava.mjc.Main;
import org.multijava.mjc.MjcLexer;
import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.MjcOptions;
import org.multijava.mjc.MjcParser;
import org.multijava.mjc.ParsingController;
import org.multijava.util.FormattedException;
import org.multijava.util.compiler.CompilerMessages;


/**
 * This class creates the test classes after receiving command
 * from command line.
 * @author Rinkesh Nagmoti. 
 * @version 1.0
 * Some of the code is taken from MultiJava open source project.
 */
public class MainClass extends Main
{

  /**
   * This method is the entry point for the tool.
   * @param the_args 
   */
  public static void main(final String[]/*@ not null @*/ the_args)
  {

    final MainClass my_Main = new MainClass();
    final File parsedArguments = new File(the_args[0]);
    final JCompilationUnitType jType = my_Main.parseFile(parsedArguments);
    final JTypeDeclarationType[] decl = jType.typeDeclarations();
    final String file = "C:\test.java";
    final TestClassGenerator my_testClass = new TestClassGenerator(file);
    my_testClass.createTest(decl[0], jType);

  }

/** Copied from multijava Main class to check the functionality of Test class generator.
 * @param the_file
 * @return JCompilationUnitType
 */
  protected JCompilationUnitType parseFile(final File the_file)
  {
    Reader buffer;
         try {
             buffer = new BufferedReader(new FileReader( the_file ));
         } catch (IOException e) {
             reportTrouble(e);
             return null;
         }

         MjcLexer mjLexer;
         JavadocLexer docLexer;
         MjcParser parser = null;
         JCompilationUnitType unit;

         // Used to switch lexers.  Aliases are created within the
         // lexer instances.
         ParsingController parsingController;

         Long duration = null;
         long lastTime = System.currentTimeMillis();

	    setAllowUniverses( options.universesx() ); // WMD

         parsingController = new ParsingController( buffer, the_file );
         mjLexer = new MjcLexer( parsingController,
                                 options.source().equals("1.4"),
                                 options.multijava(),
				    allowUniverseKeywords, // WMD
                                 MainClass.this );
         docLexer = new JavadocLexer( parsingController );

         try {
             parsingController.addInputStream( mjLexer, "multijava" );
             parsingController.addInputStream( docLexer, "javadoc" );
             parsingController.selectInitial( "multijava" );
             if (!parseJavadoc) {
                 parsingController.discardAllTokensFor( "javadoc" );
             }

             parser = 
                 new MjcParser( MainClass.this, 
                                parsingController.initialOutputStream(),
                                parsingController, 
                                options.generic(),
                                options.multijava(), 
                                options.relaxed(), 
				   allowUniverseKeywords, // WMD
                                parseJavadoc );

             unit = parser.jCompilationUnit();
             unit.cachePassParameters( MainClass.this, destination );
         } catch( ParsingController.ConfigurationException e ) {
             reportTrouble(new FormattedException( MjcMessages.PARSER_INITIALIZATION_PROBLEM,
                     the_file.getName(), e.getMessage() ));
             noteError();
             unit = null;
         } catch( antlr.ANTLRException e ) {
             reportTrouble( parser.beautifyParserError(e) );
             noteError();
             unit = null;
         } catch( Exception e ) {
		reportTrouble(e);
             e.printStackTrace();
             unit = null;
         } finally {
      duration = Long.valueOf(System.currentTimeMillis() - lastTime);
             try {
                 buffer.close();
             } catch(IOException e) {
                 reportTrouble( e );
             }
         }

         if(verboseMode()) {
             inform( CompilerMessages.FILE_PARSED, the_file.getPath(), 
                     duration );
         }

         return unit;
     }
	 //------------
	 //DATA MEMBERS
	 //------------
	 
    private MjcOptions options;
}

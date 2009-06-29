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
import antlr.*;
import org.multijava.util.FormattedException;
import org.multijava.util.compiler.CompilerMessages;


/**
 * This class creates the test classes after receiving command
 * from command line.
 * @author Rinkesh Nagmoti.
 * Some of the code is taken from MultiJava open source project.
 */
public class MainClass extends Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {

		MainClass m = new MainClass();
		File parsedArguments = new File(args[0]);
		JCompilationUnitType jType = m.parseFile(parsedArguments);
		JTypeDeclarationType[] decl = jType.typeDeclarations();
		String file = "C:\test.java";
		TestClassGenerator testClass = new TestClassGenerator(file);
		testClass.createTest(decl[0], jType);

	}
	
// Copied from multijava Main class to check the functionality of Test class generator.
	 protected JCompilationUnitType parseFile(File file) {
         Reader buffer;

         try {
             buffer = new BufferedReader(new FileReader( file ));
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

         parsingController = new ParsingController( buffer, file );
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
                     file.getName(), e.getMessage() ));
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
             duration = new Long( System.currentTimeMillis() - lastTime );
             try {
                 buffer.close();
             } catch(IOException e) {
                 reportTrouble( e );
             }
         }

         if(verboseMode()) {
             inform( CompilerMessages.FILE_PARSED, file.getPath(), 
                     duration );
         }

         return unit;
     }
	 //------------
	 //DATA MEMBERS
	 //------------
	 
    private MjcOptions options;
}

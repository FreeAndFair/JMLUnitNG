/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjmlunit.clops.CmdOptionsOptionStore;
import org.jmlspecs.openjmlunit.clops.CmdOptionsParser;
import org.jmlspecs.openjmlunit.generator.ClassInfo;
import org.jmlspecs.openjmlunit.generator.InfoFactory;
import org.jmlspecs.openjmlunit.generator.MethodInfo;
import org.jmlspecs.openjmlunit.generator.TestClassGenerator;
import org.jmlspecs.openjmlunit.generator.XMLGenerator;

/**
 * The main executable.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public final class Main {
  /**
   * The default output directory.
   */
  private static final String DEF_OUTPUT_DIR = ".";
  /**
   * The separator for classpath entries.
   */
  private static final char CLASSPATH_SEPERATOR = ';';
  /**
   * The extention for java source files.
   */
  private static final String JAVA_EXT = ".java";

  /**
   * Private constructor to prevent initialization.
   */
  private Main() {
  }

  /**
   * Tool entry point. Test bed for now.
   * 
   * @param the_args Arguments from the command line.
   */
  public static void main(final String[] the_args) {
    CmdOptionsParser clops;
    try {
      clops = new CmdOptionsParser();
      clops.parse(the_args);
      final CmdOptionsOptionStore opts = clops.getOptionStore();
      if (opts.isHelpSet()) {
        printHelp();
        System.exit(1);
      }

      final List<File> file_list = new LinkedList<File>();
      // TODO: Check for _any_ errors in either list set or package set and
      // report failure.
      if (opts.isListSet() || opts.isPackageSet()) {
        if (opts.isListSet()) {
          file_list.addAll(opts.getList());
        }
        if (opts.isPackageSet()) {
          final List<File> all_packages = opts.getPackage();
          for (int cnt = 0; cnt < all_packages.size(); cnt++) {

            final File[] all_packed_files = all_packages.get(cnt).listFiles();
            for (int k = 0; k < all_packed_files.length; k++) {
              if (all_packed_files[k].getPath().endsWith(JAVA_EXT)) {
                file_list.add(all_packed_files[k]);
              }
            }
          }
        }
      } else {
        System.err.println("Invalid files or packages.");
        System.exit(1);
      }
      String classpath;
      if (opts.isClasspathSet()) {
        final List<File> path_list = opts.getClasspath();
        final StringBuffer sb = new StringBuffer();
        for (File f : path_list) {
          sb.append(f.getAbsolutePath());
          sb.append(CLASSPATH_SEPERATOR);
        }
        classpath = sb.toString();
      } else {
        classpath = System.getenv("CLASSPATH");
      }
      final String[] arg =
          new String[] {"-noPurityCheck", "-noInternalSpecs", "-cp", classpath};
      final API api = new API(arg);
      final List<JmlCompilationUnit> units = api.parseFiles(file_list.toArray(new File[0]));
      final int numOfErrors = api.enterAndCheck(units);
      if (numOfErrors > 0) {
        System.err.println("Encountered " + numOfErrors + " errors.");
      } else {
        final Writer write = new OutputStreamWriter(System.out);
        System.out.println("Units: " + units.size());
        for (JmlCompilationUnit unit : units) {
          final ClassInfo info = InfoFactory.getClassInfo(unit);
          System.out.println("Name: " + info.getShortName());
          System.out.println("Parent Name: " + info.getSuperclassInfo().getShortName());
          System.out.println("Prot Level: " + info.getProtectionLevel().toString());
          System.out.println("Testable methods:");
          for (MethodInfo m : info.getTestableMethods()) {
            System.out.println("Method Name: " + m.getName() + " Ret Type: " +
                               m.getReturnType() + " Prot Level: " +
                               m.getProtectionLevel().toString());
          }
          XMLGenerator.generateXML(info, write);
          final TestClassGenerator generator = new TestClassGenerator();
          generator.generateTestClass(info, write);
          write.flush();
        }
      }
    } catch (final InvalidOptionPropertyValueException e1) {
      System.err.println("Invalid clops option file.");
      e1.printStackTrace();
    } catch (final AutomatonException e) {
      System.err.println("Automation Exception: " + e.getLocalizedMessage());
      e.printStackTrace();
    } catch (final InvalidOptionValueException e) {
      System.err.println(e.getLocalizedMessage());
    } catch (final IOException e) {
      System.err.println("IO Error while parsing file: " + e.getLocalizedMessage());
    }
  }

  /**
   * Print usage to standard out.
   */
  protected static void printHelp() {
    System.out.println("Generates TestNG tests for Java source code.");
    System.out.println();
    System.out.println("java -j openjmlunit.jar [OPTION] ... -f FILE,[FILE]...");
    System.out.println("-c <directory-list>, --classpath <directory-list> :  Use the "
                       + "given string as the CLASSPATH during compilation. By default"
                       + "the value of the environment variable CLASSPATH is used instead.");
    System.out.println("-d, --dest [DIRECTORY] : Specify the oputput directory "
                       + "for generated files.");
    System.out.println("-dep, --deprication : Test for Depricated members.");
    System.out.println("-E : Universe type system.");
    System.out.println("-f, --files FILE,[FILE]... : Comma-seperated list of files "
                       + "for test generation.");
    System.out.println("-h, --help : To see command line options.");
    System.out.println("-p, --package : To specify the files for testing"
                       + " with OpenJMLUnit.");
    System.out.println("-s, --safemath : Report Integral Arithmatic Overflow.");
    System.out.println("-u, --universes : Enable universe type modifiers and full"
                       + " type checking.");
    System.out.println("-v, --verbose : Display verbose information during compilation.");
    System.out.println("-inherited : Generate tests for inherited methods.");
    System.out.println("-public : Generates tests only for public methods.");
    System.out.println("-protected : Generates tests for public and protected methods.");
  }
}

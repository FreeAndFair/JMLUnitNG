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

package org.jmlspecs.jmlunitng;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.antlr.stringtemplate.StringTemplate;
import org.antlr.stringtemplate.StringTemplateGroup;
import org.jmlspecs.jmlunitng.clops.JMLUnitNGOptionStore;
import org.jmlspecs.jmlunitng.clops.JMLUnitNGParser;
import org.jmlspecs.jmlunitng.generator.ClassInfo;
import org.jmlspecs.jmlunitng.generator.InfoFactory;
import org.jmlspecs.jmlunitng.generator.MethodInfo;
import org.jmlspecs.jmlunitng.generator.ProtectionLevel;
import org.jmlspecs.jmlunitng.generator.TestClassGenerator;
import org.jmlspecs.jmlunitng.util.StringTemplateUtil;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

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
  private static final String DEF_OUTPUT_DIR = "";
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
    JMLUnitNGParser clops;
    try {
      clops = new JMLUnitNGParser();
      clops.parse(the_args);
      final JMLUnitNGOptionStore opts = clops.getOptionStore();
      if (opts.isHelpSet() || opts.getFiles().size() == 0) {
        printHelp();
        System.exit(0);
      }
      if (opts.isRACVersionSet()) {
        // see if a valid RAC version was chosen
        if (!TestClassGenerator.VALID_RAC_VERSIONS.contains
            (opts.getRACVersion())) {
          System.err.println("Invalid RAC version specified. Valid versions are: ");
          for (String s : TestClassGenerator.VALID_RAC_VERSIONS) {
            System.err.println(s + " ");
          }
          System.exit(1);
        }
      }
      final List<File> file_list = filesToProcess(opts);
      final String classpath = generateClasspath(opts);
      final String specspath = generateSpecspath(opts);
      final String[] arg =
          new String[] {"-noPurityCheck", "-noInternalSpecs", 
                        "-cp", classpath, "-specspath", specspath};
      final API api = new API(arg);
      final List<JmlCompilationUnit> units = 
        api.parseFiles(file_list.toArray(new File[0]));
      final int numOfErrors = api.enterAndCheck(units);
      if (numOfErrors > 0) {
        System.err.println("Encountered " + numOfErrors + " errors.");
      } else {
        for (JmlCompilationUnit unit : units) {
          processCompilationUnit(opts, unit);
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
   * Returns a list of files from the given set of options
   * @param the_options The command-line options.
   * @return A list of files to be processed.
   */
  private static List<File> filesToProcess(final JMLUnitNGOptionStore the_options) {
    final Set<File> file_set = new HashSet<File>();
    if (the_options.isFilesSet()) {
      addFilesToSet(the_options.getFiles(), file_set);
    }
    if (the_options.isDashFilesSet()) {
      addFilesToSet(the_options.getDashFiles(), file_set);
    }
    if (file_set.isEmpty()) {
      System.err.println("Error: no Java files specified.");
      System.exit(1);
    }
    return new ArrayList<File>(file_set);
  }
  
  /**
   * Adds all the Java files in the specified list of files/directories to
   * the specified set of files.
   * 
   * @param the_search_list The list to search.
   * @param the_add_set The set to add found files to.
   */
  private static void addFilesToSet(final List<File> the_search_list, 
                                     final Set<File> the_add_set) {
    for (File f : the_search_list) {
      if (f.isDirectory()) {
        the_add_set.addAll(findJavaFiles(f));
      } else if (f.getPath().endsWith(JAVA_EXT)) {
        the_add_set.add(f);
      } // don't add non-java files to the list
    }
  }
  /**
   * Returns a list of files in all subdirectories of the given folder.
   * @param A File object representing the directory to parse.
   * @param A List of Java files.
   */
  //@ requires the_directory.isDirectory();
  private static List<File> findJavaFiles(final File the_directory) {
    final List<File> result = new LinkedList<File>();
    final File[] all_packed_files = the_directory.listFiles();
    for (int k = 0; k < all_packed_files.length; k++) {
      if (all_packed_files[k].isDirectory()) {
        result.addAll(findJavaFiles(all_packed_files[k]));
      } else if (all_packed_files[k].getPath().endsWith(JAVA_EXT)) {
        result.add(all_packed_files[k]);
      }
    }
    return result;
  }
  
  /**
   * Extracts the classpath from the command line options.
   * @param the_options The command-line options.
   * @return The final classpath.
   */
  private static String generateClasspath(final JMLUnitNGOptionStore the_options) {
    String classpath;
    if (the_options.isClasspathSet()) {
      final List<File> path_list = the_options.getClasspath();
      final StringBuffer sb = new StringBuffer();
      for (File f : path_list) {
        sb.append(f.getAbsolutePath());
        sb.append(File.pathSeparator);
      }
      classpath = sb.toString();
    } else {
      classpath = System.getenv("CLASSPATH");
      if (classpath == null) {
        classpath = "";
      }
    }
    return classpath;
  }
  
  /**
   * Extracts the specpath from the command line options.
   * @param the_options The command-line options.
   * @return The final specpath.
   */
  private static String generateSpecspath(final JMLUnitNGOptionStore the_options) {
    String specspath;
    if (the_options.isSpecspathSet()) {
      final List<File> path_list = the_options.getSpecspath();
      final StringBuffer sb = new StringBuffer();
      for (File f : path_list) {
        sb.append(f.getAbsolutePath());
        sb.append(File.pathSeparator);
      }
      specspath = sb.toString();
    } else {
      specspath = System.getenv("SPECSPATH");
      if (specspath == null) {
        specspath = "";
      }
    }
    return specspath;
  }
  
  /**
   * Performs all source processing of the given compilation unit.
   * @param the_options The command-line options.
   * @param the_unit The compilation unit to process.
   * @throws IOException Thrown if source output fails.
   */
  private static void processCompilationUnit(final JMLUnitNGOptionStore the_options, final JmlCompilationUnit the_unit) throws IOException {
    final ClassInfo info = InfoFactory.getClassInfo(the_unit);
    //debug output
    System.out.println("Name: " + info.shortName());
    System.out.println("Parent Name: " + info.getSuperclassInfo().shortName());
    System.out.println("Prot Level: " + info.getProtectionLevel().toString());
    System.out.println("Testable Methods:");
    for (MethodInfo m : info.getTestableMethods()) {
      System.out.println("Method Name: " + m.name() + " Ret Type: " +
                         m.returnType().fullyQualifiedName() + " Prot Level: " +
                         m.protectionLevel().toString());
    }
    System.out.println("Inherited Methods:");
    for (MethodInfo m : info.getInheritedMethods()) {
      System.out.println("Method Name: " + m.name() + " Ret Type: " +
                         m.returnType().fullyQualifiedName() + " Prot Level: " +
                         m.protectionLevel().toString());      
    }
    if (info.isAbstract())
    {
      System.out.println("Abstract class, no test class generated");
      return;
    }
    //file generation
    ProtectionLevel level_to_test = ProtectionLevel.PUBLIC;
    if (the_options.isProtectedSet())
    {
      level_to_test = ProtectionLevel.PROTECTED;
    }
    if (the_options.isPackageSet())
    {
      level_to_test = ProtectionLevel.NO_LEVEL;
    }
    String rac_version = TestClassGenerator.DEF_RAC_VERSION;
    if (the_options.isRACVersionSet()) {
      rac_version = the_options.getRACVersion();
    }
    final TestClassGenerator generator = 
      new TestClassGenerator(level_to_test, 
                             the_options.isInheritedSet(),
                             the_options.isDeprecationSet(),
                             the_options.isReflectionSet(),
                             rac_version);
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("shared_java");
    final StringTemplate testClassNameTemplate = group.lookupTemplate("testClassName");
    testClassNameTemplate.setAttribute("class", info);
    final StringTemplate dataClassNameTemplate = group.lookupTemplate("dataClassName");
    dataClassNameTemplate.setAttribute("class", info);
    final String outputDir = generateDestinationDirectory(the_options, the_unit);
    if (new File(outputDir).mkdirs()) {
      final FileWriter testClassWriter = new FileWriter(new File(outputDir + testClassNameTemplate.toString() + ".java"));
      final FileWriter testDataClassWriter = new FileWriter(new File(outputDir + dataClassNameTemplate.toString() + ".java"));
      generator.generateClasses(info, testClassWriter, testDataClassWriter);
      testClassWriter.close();
      testDataClassWriter.close();
    } else {
      System.err.println("Directory creation failed.");
      System.exit(1);
    }
  }
  
  /**
   * Generates the destination filename of the given JmlCompilationUnit for the given options.
   * @param the_options The command-line options.
   * @param the_unit The JmlCompilationUnit for which to generate a filename
   */
  private static String generateDestinationDirectory(final JMLUnitNGOptionStore the_options, final JmlCompilationUnit the_unit) {
    String outputDir = DEF_OUTPUT_DIR;
    if (the_options.isDestinationSet()) {
      final StringBuilder sb = new StringBuilder(the_options.getDestination());
      if (!(outputDir.endsWith("\\") || outputDir.endsWith("/"))) {
        sb.append("/");
      }
      sb.append(the_unit.getPackageName().toString().replace('.', '/'));
      if (!(outputDir.endsWith("\\") || outputDir.endsWith("/"))) {
        sb.append("/");
      }
      outputDir = sb.toString();
    } else {
      outputDir = new File(the_unit.getSourceFile().toUri().getPath()).getParent() + "/";
    }
    return outputDir;
  }

  /**
   * Print usage to standard out.
   */
  protected static void printHelp() {
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("help");
    final StringTemplate t = group.getInstanceOf("help_msg");
    System.out.println(t.toString());
  }
}

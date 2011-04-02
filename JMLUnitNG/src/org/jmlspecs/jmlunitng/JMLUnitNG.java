/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
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
import org.jmlspecs.jmlunitng.generator.ProtectionLevel;
import org.jmlspecs.jmlunitng.generator.TestClassGenerator;
import org.jmlspecs.jmlunitng.util.JavaSuffixFilter;
import org.jmlspecs.jmlunitng.util.Logger;
import org.jmlspecs.jmlunitng.util.StringTemplateUtil;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

/**
 * The main executable.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version February 2011
 */
public final class JMLUnitNG implements Runnable {
  /**
   * The string to be prepended to the reported version.
   */
  private static final String VERSION_STRING = "1.0b3c";
  
  /**
   * The raw SVN revision string.
   */
  private static final String RAW_SVN_REV = "$Rev$";
  
  /**
   * The default output directory.
   */
  private static final String DEF_OUTPUT_DIR = "";
  
  /**
   * The extension for Java source files.
   */
  public static final String JAVA_SUFFIX = ".java";

  /**
   * The extension for Java class files.
   */
  public static final String CLASS_SUFFIX = ".class";
  
  /**
   * The command line options store to be used.
   */
  private final JMLUnitNGOptionStore my_opts;
  
  /**
   * The "generated by JMLUnitNG" string, used to detect 
   * JMLUnitNG-generated files.
   */
  private final String my_gen_string;
  
  /**
   * The "do not change this comment" string, used to detect 
   * JMLUnitNG-generated files.
   */
  private final String my_dnm_string;
  
  /**
   * The suffix used for data packages, used to detect 
   * JMLUnitNG-generated directories
   */
  private final String my_sp_suffix;
  
  /**
   * The set of files/directories we have cleaned on this run.
   */
  private final Set<String> my_cleaned_files = new HashSet<String>();
  
  /**
   * The set of files/directories we have created on this run.
   */
  private final Set<String> my_created_files = new HashSet<String>();
  
  /**
   * The logger to use when generating output.
   */
  private final Logger my_logger;
  
  /**
   * The time at which this instance was created.
   */
  private final long my_start_time = System.currentTimeMillis();
  
  
  /**
   * Constructs a JMLUnitNG instance with the specified command line
   * options.
   * 
   * @param the_opts The command line options store to be used.
   */
  public JMLUnitNG(final JMLUnitNGOptionStore the_opts) {
    my_opts = the_opts;
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("shared_java");
    my_gen_string = group.lookupTemplate("generatedString").toString();
    my_dnm_string = group.lookupTemplate("doNotModifyString").toString();
    my_sp_suffix = group.lookupTemplate("strategyPackageSuffix").toString();
    my_logger = new Logger(the_opts.isVerboseSet() || the_opts.isDryRunSet());
  }

  /**
   * The version string, generated from SVN properties.
   */
  public static String version() {
    final String svnRev = RAW_SVN_REV.substring(6, RAW_SVN_REV.length() - 2);
    
    return VERSION_STRING + " (" + svnRev + ")";
  }
  
  /**
   * The main method. Parses the command line arguments and runs
   * the tool.
   * 
   * @param the_args Arguments from the command line.
   */
  public static void main(final String[] the_args) {
    try {
      final JMLUnitNGParser clops = new JMLUnitNGParser();
      clops.parse(the_args);
      (new JMLUnitNG(clops.getOptionStore())).run();
    }
    catch (final InvalidOptionPropertyValueException e) {
      System.err.println("Invalid CLOPS option file.");
      e.printStackTrace();
    } catch (final AutomatonException e) {
      System.err.println("Automaton Exception: " + e.getLocalizedMessage());
      e.printStackTrace();
    } catch (final InvalidOptionValueException e) {
      System.err.println(e.getLocalizedMessage());
    }
  }
  
  /**
   * The run method. Handles the entire execution of JMLUnitNG, once
   * command line arguments have been parsed; JMLUnitNG can be run
   * programmatically by using CLOPS to parse a command line into
   * a suitable JMLUnitNGOptionStore.
   */
  public void run() {
    if (my_opts.isHelpSet() || 
        (my_opts.getFiles().size() == 0 && !my_opts.isNoGenSet())) {
      printHelp();
      Runtime.getRuntime().exit(0);
    }    
    if (my_opts.isRACVersionSet() && 
        !TestClassGenerator.VALID_RAC_VERSIONS.contains
          (my_opts.getRACVersion())) {
      printInvalidRACError();
      Runtime.getRuntime().exit(1);
    }
    if (my_opts.isDryRunSet()) {
      my_logger.println(">>> DRY RUN <<<");
    }
    if (my_opts.isCleanSet()) {
      cleanAllFiles();
    }
    try {
      processAllCompilationUnits();
    } catch (IOException e) {
      System.err.println("I/O exception occurred.");
      e.printStackTrace();
      Runtime.getRuntime().exit(1);
    }
    if (my_opts.isPruneSet()) {
      pruneAllFiles();
    }
   
    my_logger.print("Elapsed time ");
    final long end_time = (System.currentTimeMillis() - my_start_time) / 1000;
    if (end_time / 60 > 0) {
      my_logger.print((end_time / 60) + " min ");
    }
    my_logger.println((end_time % 60) + " sec");
    my_logger.println();
  }
  
  /**
   * Returns a list of files from the given set of options
   *
   * @return A list of files to be processed.
   */
  private List<File> filesToProcess() {
    final Set<File> file_set = new HashSet<File>();
    if (my_opts.isFilesSet()) {
      addFilesToSet(my_opts.getFiles(), file_set);
    }
    if (my_opts.isDashFilesSet()) {
      addFilesToSet(my_opts.getDashFiles(), file_set);
    }
    if (file_set.isEmpty()) {
      System.err.println("No Java files specified.");
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
  private void addFilesToSet(final List<File> the_search_list, 
                             final Set<File> the_add_set) {
    for (File f : the_search_list) {
      if (f.isDirectory()) {
        the_add_set.addAll(findJavaFiles(f));
      } else if (f.getPath().endsWith(JAVA_SUFFIX)) {
        try {
          the_add_set.add(f.getCanonicalFile());
        } catch (IOException e) {
          // this should never happen
          System.err.println("I/O exception while finding files.");
          e.printStackTrace();
          Runtime.getRuntime().exit(1);
        }
      } // don't add non-java files to the list
    }
  }
  
  /**
   * Returns a list of Java files in all subdirectories of the given folder,
   * ignoring files generated by JMLUnitNG.
   * 
   * @param A File object representing the directory to parse.
   * @param A List of Java files.
   */
  //@ requires the_directory.isDirectory();
  private List<File> findJavaFiles(final File the_directory) {
    final List<File> result = new LinkedList<File>();
    final File[] all_packed_files = the_directory.listFiles(JavaSuffixFilter.instance());
    for (int k = 0; k < all_packed_files.length; k++) {
      if (all_packed_files[k].isDirectory()) {
        result.addAll(findJavaFiles(all_packed_files[k]));
      } else if (isJavaSourcePath(all_packed_files[k].getPath()) &&
                 !isJMLUnitNGGenerated(all_packed_files[k])) {
        try {
          result.add(all_packed_files[k].getCanonicalFile());
        } catch (IOException e) {
          // this should never happen
          System.err.println("I/O exception while finding files.");
          e.printStackTrace();
          Runtime.getRuntime().exit(1);
        }
      }
    }
    return result;
  }
  
  /**
   * @return true if the specified pathname represents a Java file
   * that was not generated by JMLUnitNG.
   */
  private boolean isJavaSourcePath(final String the_path) {
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = 
      StringTemplateGroup.loadGroup("shared_java");
    final String testSuffix = 
      group.lookupTemplate("testClassSuffix").toString();
    final String packageSuffix = 
      group.lookupTemplate("strategyPackageSuffix").toString();

    return the_path.endsWith(JAVA_SUFFIX) &&
           !the_path.endsWith(testSuffix + JAVA_SUFFIX) &&
           !the_path.contains(packageSuffix + File.separator);
  }
  
  /**
   * Extracts the classpath from the command line options.
   *
   * @return The final classpath.
   */
  private String generateClasspath() {
    String classpath;
    if (my_opts.isClasspathSet()) {
      final List<File> path_list = my_opts.getClasspath();
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
   * Extracts the specspath from the command line options.
   *
   * @return The final specspath.
   */
  private String generateSpecspath() {
    String specspath;
    if (my_opts.isSpecspathSet()) {
      final List<File> path_list = my_opts.getSpecspath();
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
   * Processes all necessary compilation units.
   * 
   * @exception IOException if there is a problem processing compilation units.
   */
  private void processAllCompilationUnits() throws IOException {
    if (!my_opts.isNoGenSet()) {
      my_logger.println("Starting test generation");
      my_logger.println();
    }
    
    // the only reason to go to this effort if --no-gen is set is if
    // --prune is also set, so we need to find out what files to prune
    
    if (!my_opts.isNoGenSet() || my_opts.isPruneSet()) {
      final List<File> file_list = filesToProcess();
      final String classpath = generateClasspath();
      final String specspath = generateSpecspath();
      final String[] openjml_args =
          new String[] {"-noPurityCheck", "-noInternalSpecs",
                        "-cp", classpath, "-specspath", specspath};
      final API api = new API(new PrintWriter(System.err), null, openjml_args);
      final List<JmlCompilationUnit> units = 
        api.parseFiles(file_list.toArray(new File[file_list.size()]));
      final int numOfErrors = api.enterAndCheck(units);
      if (numOfErrors > 0) {
        System.err.println("Encountered " + numOfErrors + " errors.");
        Runtime.getRuntime().exit(1);
      }
      
      // get class info for all classes before generating tests for any,
      // to enable reflective generation of child classes
      
      InfoFactory.generateInfos(units, api);
      for (JmlCompilationUnit u : units) {
        processCompilationUnit(u, InfoFactory.getClassInfo(u));
        if (!my_opts.isNoGenSet()) {  
          my_logger.println();
        }
      }
    }
  }
  
  /**
   * Performs all source processing of the given compilation unit.
   *
   * @param the_unit The compilation unit to process.
   * @param the_info The class information generated from the 
   *  compilation unit.
   * @throws IOException Thrown if source output fails.
   */
  private void processCompilationUnit(final JmlCompilationUnit the_unit, 
                                      final ClassInfo the_info) 
  throws IOException {
    if (!my_opts.isNoGenSet()) {
      my_logger.print("Processing ");

      if (the_info.isInterface()) {
        my_logger.println("interface " + the_info.getFullyQualifiedName());
      } else if (the_info.isAbstract()) {
        my_logger.println("abstract class " + the_info.getFullyQualifiedName());
      } else if (the_info.isEnumeration()) {
        my_logger.println("enumeration " + the_info.getFullyQualifiedName());
      } else { // normal class
        my_logger.println("class " + the_info.getFullyQualifiedName());
      }
    }
    if (the_info.isAbstract() && the_info.getNestedClasses().isEmpty() || 
        the_info.isEnumeration()) {
      return;
    }
    String rac_version = TestClassGenerator.DEF_RAC_VERSION;
    if (my_opts.isRACVersionSet()) {
      rac_version = my_opts.getRACVersion();
    }
    final TestClassGenerator generator = 
      new TestClassGenerator(my_opts.isDryRunSet(), 
                             my_opts.isNoGenSet(),
                             my_logger,
                             levelToTest(), 
                             my_opts.isInheritedSet(),
                             my_opts.isDeprecationSet(),
                             my_opts.isReflectionSet(),
                             my_opts.isChildrenSet(),
                             rac_version);

    final String[] dirs = getDirectories(the_unit, the_info);
    String strategy_dir = dirs[0];
    for (String s : dirs) {
      final File f = new File(s);
      if (!my_opts.isNoGenSet() && !the_info.isAbstract()) { // don't create dirs for abstract classes for now
        my_logger.println("Creating directory " + f);
        if (!my_opts.isDryRunSet() && !f.mkdirs() && !f.isDirectory()) {
          System.err.println("Could not create destination directory " + f);
          Runtime.getRuntime().exit(1);
        }
      }
      my_created_files.add(f.getCanonicalPath());
      strategy_dir = s;
    }
    
    generator.generateClasses(the_info, dirs[0], strategy_dir);
    my_created_files.addAll(generator.getCreatedFiles());
  }
  
  /**
   * @param the_unit the unit being processed.
   * @return An array of directory names to create/use for the specified unit.
   */
  private String[] getDirectories(final JmlCompilationUnit the_unit,
                                  final ClassInfo the_info) {
    String[] result;
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("shared_java");
    final StringTemplate sp_template = group.lookupTemplate("strategyPackageShortName");
    sp_template.setAttribute("classInfo", the_info);

    final String output_dir = generateDestinationDirectory(the_unit);
    if (the_info.isPackaged()) {
      final String strategy_dir =  
        output_dir + sp_template.toString() + File.separator;
      result = new String[] { output_dir, strategy_dir };
    } else {
      result = new String[] { output_dir };
    }
    
    return result;
  }
  
  /**
   * Prunes all necessary files, based on the set of files we've created.
   */
  private void pruneAllFiles() {
    my_logger.println("Pruning obsolete JMLUnitNG-generated files");
    my_cleaned_files.clear();
    final Set<File> files_to_prune = new HashSet<File>();
    if (my_opts.isDestinationSet()) {
      files_to_prune.add(new File(my_opts.getDestination()));
    } else {
      files_to_prune.addAll(my_opts.getFiles());
      files_to_prune.addAll(my_opts.getDashFiles());
    }
    for (File f : files_to_prune) {
      try {
        cleanOrPruneFile(f, true);
      } catch (IOException e) {
        System.err.println("Error occurred while pruning files.");
        e.printStackTrace();
        Runtime.getRuntime().exit(1);
      }
    }
    my_logger.println("Pruning complete");
    my_logger.println();
  }
  
  /**
   * Cleans all necessary files.
   */
  private void cleanAllFiles() {
    my_logger.println("Cleaning old JMLUnitNG-generated files");
    final Set<File> files_to_clean = new HashSet<File>();
    if (my_opts.isDestinationSet()) {
      files_to_clean.add(new File(my_opts.getDestination()));
    } else {
      files_to_clean.addAll(my_opts.getFiles());
      files_to_clean.addAll(my_opts.getDashFiles());
    }
    for (File f : files_to_clean) {
      try {
        cleanOrPruneFile(f, false);
      } catch (IOException e) {
        System.err.println("Error occurred while cleaning files.");
        e.printStackTrace();
        Runtime.getRuntime().exit(1);
      }
    }
    my_logger.println("Cleaning complete");
    my_logger.println();
  }
  
  /**
   * Clean or prune the specified file/directory (recursively), by removing any 
   * JMLUnitNG-generated files and directories.
   * 
   * @param the_file The file/directory to clean.
   * @param the_prune true if we're pruning (that is, we only delete those
   * files and directories that we did not create this run) and false otherwise.
   */
  private void cleanOrPruneFile
  (final File the_file, final boolean the_prune) throws IOException {
    if (my_cleaned_files.add(the_file.getCanonicalPath()) && the_file.exists()) {
      final boolean one_of_ours = 
        isJMLUnitNGGenerated(the_file) && 
        (!the_prune || !my_created_files.contains(the_file.getCanonicalPath()));
      if (the_file.isDirectory()) {
        for (File f : the_file.listFiles(JavaSuffixFilter.instance())) {
          cleanOrPruneFile(f, the_prune);
        }
      } 
      if (one_of_ours) {
        my_logger.println("Deleting " + the_file);
        if (!my_opts.isDryRunSet() && !the_file.delete()) {
          System.err.println("Unable to delete " + the_file + ", check permissions.");
        }
        // if there's a corresponding .class file, delete that too
        if (the_file.getAbsolutePath().contains(".java"))
        {
          final File class_file = 
            new File(the_file.getAbsolutePath().replace(JAVA_SUFFIX, CLASS_SUFFIX));
          if (class_file.exists()) {
            my_logger.println("Deleting " + class_file);
            if (!my_opts.isDryRunSet() && !class_file.delete()) {
              System.err.println("Unable to delete " + the_file + ", check permissions.");
            }
          }
        }
      }
    }
  }
  
  /**
   * @param the_file The file to check.
   * @return true if the file/directory was generated by JMLUnitNG, 
   * false otherwise.
   */
  private /*@ helper @*/ boolean isJMLUnitNGGenerated(final File the_file) {
    boolean result = false;
    try {
      if (the_file.exists() && !the_file.isDirectory()) {
        // it's a file so it's generated by us if it has our comment
        final BufferedReader br = new BufferedReader(new FileReader(the_file));
        boolean gen_string_found = false;
        boolean dnm_string_found = false;
        String line = br.readLine();
        while (line != null && (!gen_string_found || !dnm_string_found)) {
          gen_string_found |= line.contains(my_gen_string);
          dnm_string_found |= line.contains(my_dnm_string);
          line = br.readLine();
        } 
        br.close();
        result = gen_string_found && dnm_string_found;
      } else if (the_file.exists()) {
        // it's a directory so it's generated by us if it has the right suffix
        result = the_file.getCanonicalPath().endsWith(my_sp_suffix);
      }
    } catch (IOException e) {
      // if we got an exception, we couldn't read the file, so let's
      // assume we didn't generate it
      result = false;
    }
    return result;
  }
  
  /**
   * @return the protection level to test, based on the command line options.
   */
  private ProtectionLevel levelToTest() {
    ProtectionLevel level = ProtectionLevel.PUBLIC;
    if (my_opts.isProtectedSet()) {
      level = ProtectionLevel.PROTECTED;
    }
    if (my_opts.isPackageSet()) {
      level = ProtectionLevel.NO_LEVEL;
    }
    return level;
  }
  
  /**
   * Generates the destination filename of the given JmlCompilationUnit for the given options.
   *   
   * @param the_unit The JmlCompilationUnit for which to generate a filename
   */
  private String generateDestinationDirectory(final JmlCompilationUnit the_unit) {
    String outputDir = DEF_OUTPUT_DIR;
    if (my_opts.isDestinationSet()) {
      final StringBuilder sb = new StringBuilder(my_opts.getDestination());
      if (!(outputDir.endsWith("\\") || outputDir.endsWith("/"))) {
        sb.append(File.separator);
      }
      if (the_unit.getPackageName() != null) {
        sb.append(the_unit.getPackageName().toString().replace('.', File.separatorChar));
      }
      if (!(outputDir.endsWith("\\") || outputDir.endsWith("/"))) {
        sb.append(File.separator);
      }
      
      outputDir = sb.toString().replace('\\', File.separatorChar);
      outputDir = outputDir.replace('/', File.separatorChar);
    } else {
      outputDir = new File(the_unit.getSourceFile().toUri().getPath()).getParent() +
                  File.separator;
    }
    return outputDir;
  }

  /**
   * Print usage to standard out.
   */
  private void printHelp() {
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("help");
    final StringTemplate t = group.getInstanceOf("help_msg");
    t.setAttribute("version", version());
    System.out.println(t.toString());
  }
  
  /**
   * Print invalid RAC error to standard error.
   */
  private void printInvalidRACError() {
    System.err.println("Invalid RAC version specified. Valid versions are: ");
    for (String s : TestClassGenerator.VALID_RAC_VERSIONS) {
      System.err.println(s + " ");
    }
  }
}

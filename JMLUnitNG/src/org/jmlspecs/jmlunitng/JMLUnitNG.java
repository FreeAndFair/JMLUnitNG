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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
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
import org.jmlspecs.jmlunitng.util.JavaSuffixFilter;
import org.jmlspecs.jmlunitng.util.StringTemplateUtil;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

/**
 * The main executable.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public final class JMLUnitNG implements Runnable {
  /**
   * The string to be prepended to the reported version.
   */
  private static final String VERSION_STRING = "1.0a1";
  
  /**
   * The raw SVN revision string.
   */
  private static final String RAW_SVN_REV = "$Rev$";
  
  /**
   * The default output directory.
   */
  private static final String DEF_OUTPUT_DIR = "";
  
  /**
   * The extension for java source files.
   */
  public static final String JAVA_SUFFIX = ".java";

  /**
   * The command line options store to be used.
   */
  private final JMLUnitNGOptionStore my_opts;
  
  /**
   * The set of files/directories we have cleaned on this run.
   */
  private final Set<String> my_cleaned_files = new HashSet<String>();
  
  /**
   * Private constructor to prevent initialization.
   * 
   * @param the_opts The command line options store to be used.
   */
  public JMLUnitNG(final JMLUnitNGOptionStore the_opts) {
    my_opts = the_opts;
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
    if (my_opts.isHelpSet() || my_opts.getFiles().size() == 0) {
      printHelp();
      Runtime.getRuntime().exit(0);
    }
    if (my_opts.isRACVersionSet() && 
        !TestClassGenerator.VALID_RAC_VERSIONS.contains
          (my_opts.getRACVersion())) {
        System.err.println("Invalid RAC version specified. Valid versions are: ");
        for (String s : TestClassGenerator.VALID_RAC_VERSIONS) {
          System.err.println(s + " ");
        }
        Runtime.getRuntime().exit(1);
    }
    if (my_opts.isCleanSet()) {
      final List<File> files_to_clean = new LinkedList<File>(my_opts.getFiles());
      files_to_clean.addAll(my_opts.getDashFiles());
      for (File f : files_to_clean) {
        try {
          cleanFile(f);
        } catch (IOException e) {
          System.err.println("Error occurred while cleaning files.");
          e.printStackTrace();
          Runtime.getRuntime().exit(1);
        }
      }
    }
    final List<File> file_list = filesToProcess();
    final String classpath = generateClasspath();
    final String specspath = generateSpecspath();
    final String[] openjml_args =
        new String[] {"-noPurityCheck", "-noInternalSpecs", 
                      "-cp", classpath, "-specspath", specspath};
    try {
      final API api = new API(openjml_args);
      final List<JmlCompilationUnit> units = 
        api.parseFiles(file_list.toArray(new File[0]));
      final int numOfErrors = api.enterAndCheck(units);
      if (numOfErrors > 0) {
        System.err.println("Encountered " + numOfErrors + " errors.");
      } else {
        for (JmlCompilationUnit unit : units) {
          processCompilationUnit(unit);
        }
      }
    } catch (IOException e) {
      System.err.println("I/O exception occurred.");
      e.printStackTrace();
      Runtime.getRuntime().exit(1);
    }
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
      System.err.println("Error: no Java files specified.");
      Runtime.getRuntime().exit(1);
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
   * Returns a list of files in all subdirectories of the given folder.
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
      } else if (isJavaSourcePath(all_packed_files[k].getPath())) {
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
   * Performs all source processing of the given compilation unit.
   *
   * @param the_unit The compilation unit to process.
   * @throws IOException Thrown if source output fails.
   */
  private void processCompilationUnit(final JmlCompilationUnit the_unit) 
  throws IOException {
    final ClassInfo class_info = InfoFactory.getClassInfo(the_unit);
    
    if (class_info == null) {
      return;
    }
    
    if (my_opts.isVerboseSet()) {
      classInfoVerbose(class_info);
    }
  
    if (class_info.isAbstract()) {
      return;
    }
    
    String rac_version = TestClassGenerator.DEF_RAC_VERSION;
    if (my_opts.isRACVersionSet()) {
      rac_version = my_opts.getRACVersion();
    }
    final TestClassGenerator generator = 
      new TestClassGenerator(levelToTest(), 
                             my_opts.isInheritedSet(),
                             my_opts.isDeprecationSet(),
                             my_opts.isReflectionSet(),
                             rac_version);
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("shared_java");
    final StringTemplate spNameTemplate = group.lookupTemplate("strategyPackageShortName");
    spNameTemplate.setAttribute("classInfo", class_info);

    final String outputDir = generateDestinationDirectory(the_unit);
    final String strategyOutputDir = 
      outputDir + spNameTemplate.toString() + File.separator;
    final File[] dirs = new File[] { new File(outputDir), new File(strategyOutputDir) };

    if (!my_opts.isNoGenSet()) {
      for (File f : dirs) {
        System.err.println("Creating directory " + f);
        if (!f.mkdirs() && !f.isDirectory()) {
          System.err.println("Could not create destination directory " + f);
          Runtime.getRuntime().exit(1);
        }
      }
    
      generator.generateClasses(class_info, outputDir);
    }
  }
  
  /**
   * Clean the specified file/directory (recursively), by removing any 
   * JMLUnitNG-generated files and directories.
   * 
   * @param the_dir The directory to clean.
   */
  private void cleanFile(final File the_file) throws IOException {
    StringTemplateUtil.initialize();
    final StringTemplateGroup group = StringTemplateGroup.loadGroup("shared_java");
    final String genString = group.lookupTemplate("generatedString").toString();
    final String dnmString = group.lookupTemplate("doNotModifyString").toString();
    final String spSuffix = group.lookupTemplate("strategyPackageSuffix").toString();

    if (my_cleaned_files.add(the_file.getCanonicalPath())) {
      if (the_file.isDirectory()) {
        for (File f : the_file.listFiles(JavaSuffixFilter.instance())) {
          cleanFile(f);
        }
      } else {
        // for each file, we will delete it if it has a JMLUnitNG-generated
        // comment at the top
        final BufferedReader br = new BufferedReader(new FileReader(the_file));
        boolean genStringFound = false;
        boolean dnmStringFound = false;
        String line = br.readLine();
        while (line != null && (!genStringFound || !dnmStringFound)) {
          genStringFound |= line.contains(genString);
          dnmStringFound |= line.contains(dnmString);
          line = br.readLine();
        }
        // if we found both strings, delete the file
        if (genStringFound && dnmStringFound) {
          System.err.println("Deleting " + the_file);
          if (!the_file.delete()) {
            System.err.println("Unable to delete " + the_file + ", check permissions.");
          }
        }
      }
      // if the directory is a JMLUnitNG-created directory, delete it too
      // (it should be empty by now)
      if (the_file.getCanonicalPath().endsWith(spSuffix)) {
        System.err.println("Deleting directory " + the_file);
        if (!the_file.delete()) {
          System.err.println("Unable to delete " + the_file + ", check permissions.");
        }
      }
    }
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
   * Outputs verbose information for a class's test generation stage.
   * 
   * @param the_class_info The class info.
   */
  private void classInfoVerbose(final ClassInfo the_class_info) {
    System.out.println("Name: " + the_class_info.getShortName());
    if (the_class_info.getParent() != null) {
      System.out.println("Parent Name: " + the_class_info.getParent().getShortName());
    }
    System.out.println("Prot Level: " + the_class_info.getProtectionLevel().toString());
    System.out.println("Testable Methods:");
    for (MethodInfo m : the_class_info.getTestableMethods()) {
      System.out.println(m.getProtectionLevel() + " " + m);
    }
    System.out.println("Inherited Methods:");
    for (MethodInfo m : the_class_info.getInheritedMethods()) {
      System.out.println(m.getProtectionLevel() + " " + m);      
    }
    if (the_class_info.isAbstract())
    {
      System.out.println("Abstract class, no test class generated");
    }
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
      sb.append(the_unit.getPackageName().toString().replace('.', '/'));
      if (!(outputDir.endsWith("\\") || outputDir.endsWith("/"))) {
        sb.append(File.separator);
      }
      
      outputDir = sb.toString().replace("\\", File.separator);
      outputDir = outputDir.replace("/", File.separator);
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
}

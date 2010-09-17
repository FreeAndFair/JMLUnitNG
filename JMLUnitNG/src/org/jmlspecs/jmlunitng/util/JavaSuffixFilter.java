package org.jmlspecs.jmlunitng.util;

import java.io.File;
import java.io.FileFilter;

import org.jmlspecs.jmlunitng.JMLUnitNG;

/**
 * A filename filter that accepts ".java" files.
 * 
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public class JavaSuffixFilter implements FileFilter {
  /**
   * An instance of this filter, since it always does exactly
   * the same thing.
   */
  private static final JavaSuffixFilter INSTANCE = new JavaSuffixFilter();
  
  /**
   * @return an instance of this filter.
   */
  public static JavaSuffixFilter instance() {
    return INSTANCE;
  }
  
  /**
   * Checks to see if the specified file ends in the Java suffix, 
   * as specified in JMLUnitNG.JAVA_SUFFIX, or is a directory.
   * 
   * @param the_file The file to check.
   * @return true if the file is a Java file or directory, false
   *  otherwise.
   */
  @Override
  public boolean accept(final File the_file) {
    return the_file.getName().endsWith(JMLUnitNG.JAVA_SUFFIX) ||
           the_file.isDirectory();
  }
}

/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.util;

import java.io.File;
import java.io.FileFilter;

import org.jmlspecs.jmlunitng.JMLUnitNG;

/**
 * A file filter that accepts ".java" files and all directories.
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
   * @return What is the shared suffix filter?
   */
  public /*@ pure non_null @*/ static JavaSuffixFilter instance() {
    return INSTANCE;
  }
  
  /**
   * @param the_file The file to check.
   * @return Is the_file either a file with name ending in ".java" or 
   *  a directory?
   */
  @Override
  public /*@ pure @*/ boolean accept(final File the_file) {
    return the_file.getName().endsWith(JMLUnitNG.JAVA_SUFFIX) ||
           the_file.isDirectory();
  }
}

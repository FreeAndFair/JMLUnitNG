/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng;

import java.io.File;
import java.util.List;

import org.jmlspecs.jmlunitng.util.ProtectionLevel;

/**
 * A class that encapsulates the various configuration options for
 * JMLUnitNG. This abstracts away the particular command line argument
 * parser, primarily for convenience in using JMLUnitNG programmatically.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public class JMLUnitNGConfiguration {
  /**
   * The destination path.
   */
  private String my_destination;
  
  /**
   * The list of files to process.
   */
  private List<File> my_files;
  
  /**
   * The list of directories and files comprising the classpath.
   */
  private List<File> my_classpath;
  
  /**
   * The list of directories and files comprising the specspath.
   */
  private List<File> my_specspath;
  
  /**
   * The RAC version to use.
   */
  private String my_rac_version;
  
  /**
   * A flag indicating whether the "--deprecation" option is on;
   * the default value is off.
   */
  private boolean my_deprecation;
  
  /**
   * A flag indicating whether the "--inherited" option is on;
   * the default value is off.
   */
  private boolean my_inherited;
  
  /**
   * The protection level to scan (derived from the "--public", 
   * "--protected", "--package" options).
   */
  private ProtectionLevel my_protection_level;
  
  /**
   * A flag indicating whether the "--reflection" option is on; 
   * the default value is off.
   */
  private boolean my_reflection;
  
  /**
   * A flag indicating whether the "--children" option is on; 
   * the default value is off.
   */
  private boolean my_children;

  /**
   * A flag indicating whether the "--verbose" option is on; 
   * the default value is off.
   */
  private boolean my_verbose;

}

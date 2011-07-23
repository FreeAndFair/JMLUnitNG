/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
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
   * The destination path. This is the empty String by default, meaning 
   * that the destination path is the same as the source path.
   */
  private String my_destination = "";
  
  /**
   * The list of files to process. Empty by default.
   */
  private List<File> my_files = new ArrayList<File>();
  
  /**
   * The list of directories and files comprising the classpath.
   * Empty by default.
   */
  private List<File> my_classpath = new ArrayList<File>();
  
  /**
   * The list of directories and files comprising the specspath.
   * Empty by default.
   */
  private List<File> my_specspath = new ArrayList<File>();
  
  /**
   * The RAC version to use. The default value is "jml4".
   */
  private String my_rac_version = "jml4";
  
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
   * "--protected", "--package" options). The default level is PUBLIC.
   */
  private ProtectionLevel my_protection_level = ProtectionLevel.PUBLIC;
  
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
   * A flag indicating whether the "--literals" option is on; 
   * the default value is off.
   */
  private boolean my_literals;
  
  /**
   * A flag indicating whether the "--spec-literals" option is on;
   * the default value is off.
   */
  private boolean my_spec_literals;
  
  /**
   * A flag indicating whether the "--clean" option is on; the
   * default value is off.
   */
  private boolean my_clean;
  
  /**
   * A flag indicating whether the "--prune" option is on; the 
   * default value is off.
   */
  private boolean my_prune;
  
  /**
   * A flag indicating whether the "--no-gen" option is on; the
   * default value is off.
   */
  private boolean my_no_gen;
  
  /**
   * A flag indicating whether the "--dry-run" option is on; the
   * default value is off.
   */
  private boolean my_dry_run;
  
  /**
   * A flag indicating whether the "--verbose" option is on; 
   * the default value is off.
   */
  private boolean my_verbose;

  // default constructor
  
  // destination settings
  
  /**
   * Sets the output directory for generated classes; the empty string
   * results in generated classes being generated in the same directories 
   * as the corresponding Java source files.
   * 
   * @param the_destination The destination directory.
   */
  public void setDestination(final String the_destination) {
    my_destination = the_destination;
  }
  
  /**
   * @return the output directory for generated classes, or the
   * empty string if they are generated in the same directories as the
   * corresponding Java source files.
   */
  public /*@ pure @*/ String getDestination() {
    return my_destination;
  }
  
  // files settings
  
  /**
   * Sets the list of directories and Java files to process.
   * 
   * @param the_files The list of directories and files.
   */
  public void setFiles(final List<File> the_files) {
    my_files = new ArrayList<File>(the_files);
  }
  
  /**
   * @return an unmodifiable view of the list of directories and 
   *  Java files to process.
   */
  public /*@ pure @*/ List<File> getFiles() {
    return Collections.unmodifiableList(my_files);
  }

  // classpath settings
  
  /**
   * Sets the list of directories and Jar files to use as the classpath
   * during parsing.
   * 
   * @param the_classpath The classpath list.
   */
  public void setClasspath(final List<File> the_classpath) {
    my_classpath = new ArrayList<File>(the_classpath);
  }
  
  /**
   * @return an unmodifiable view of the list of directories and Jar files
   * to use as the classpath during parsing.
   */
  public /*@ pure @*/ List<File> getClasspath() {
    return Collections.unmodifiableList(my_classpath);
  }
  
  // specs settings
  
  /**
   * Sets the list of directories and Jar files to use as the specspath
   * during parsing.
   * 
   * @param the_specspath The specspath list.
   */
  public void setSpecspath(final List<File> the_specspath) {
    my_specspath = new ArrayList<File>(the_specspath);
  }
  
  /**
   * @return an unmodifiable view of the list of directories and Jar files
   * to use as the specspath during parsing.
   */
  public /*@ pure @*/ List<File> getSpecspath() {
    return Collections.unmodifiableList(my_specspath);
  }
  
  // RAC version setting
  
  /**
   * Sets the RAC version to generate code for. See JMLUnitNG help
   * for the currently-supported values; using an unsupported value will
   * fail to generate code.
   * 
   * @param the_rac_version The RAC version. The empty string will
   * cause JMLUnitNG to use its default RAC version.
   */
  public void setRACVersion(final String the_rac_version) {
    my_rac_version = the_rac_version;
  }
  
  /**
   * @return the RAC version to generate code for.
   */
  public /*@ pure @*/ String getRACVersion() {
    return my_rac_version;
  }
  
  // deprecation setting
  
  /**
   * Sets the "--deprecation" option.
   * 
   * @param the_deprecation The new setting.
   */
  public void setDeprecation(final boolean the_deprecation) {
    my_deprecation = the_deprecation;
  }
  
  /**
   * @return the "--deprecation" setting.
   */
  public /*@ pure @*/ boolean isDeprecationSet() {
    return my_deprecation;
  }
  
  // inherited setting
  
  /**
   * Sets the "--inherited" option.
   * 
   * @param the_inherited The new setting.
   */
  public void setInherited(final boolean the_inherited) {
    my_inherited = the_inherited;
  }
  
  /**
   * @return the "--inherited" setting.
   */
  public /*@ pure @*/ boolean isInheritedSet() {
    return my_inherited;
  }
  
  // protection level setting
  
  /**
   * Sets the protection level to generate tests for.
   * 
   * @param the_protection_level The new protection level.
   */
  public void setProtectionLevel(final ProtectionLevel the_protection_level) {
    my_protection_level = the_protection_level;
  }
  
  /**
   * @return the protection level to generate tests for.
   */
  public /*@ pure @*/ ProtectionLevel getProtectionLevel() {
    return my_protection_level;
  }
  
  // reflection setting
  
  /**
   * Sets the "--reflection" option.
   * 
   * @param the_reflection The new setting.
   */
  public void setReflection(final boolean the_reflection) {
    my_reflection = the_reflection;
  }
  
  /**
   * @return the "--reflection" setting.
   */
  public /*@ pure @*/ boolean isReflectionSet() {
    return my_reflection;
  }
  
  // children setting
  
  /**
   * Sets the "--children" option.
   * 
   * @param the_children The new setting.
   */
  public void setChildren(final boolean the_children) {
    my_children = the_children;
  }
  
  /**
   * @return the "--children" setting.
   */
  public /*@ pure @*/ boolean isChildrenSet() {
    return my_children;
  }
  
  // literals setting
  
  /**
   * Sets the "--literals" option.
   * 
   * @param the_literals The new setting.
   */
  public void setLiterals(final boolean the_literals) {
    my_literals = the_literals;
  }
  
  /**
   * @return the "--literals" setting.
   */
  public /*@ pure @*/ boolean isLiteralsSet() {
    return my_literals;
  }
  
  // spec_literals setting
  
  /**
   * Sets the "--spec_literals" option.
   * 
   * @param the_spec_literals The new setting.
   */
  public void setSpecLiterals(final boolean the_spec_literals) {
    my_spec_literals = the_spec_literals;
  }
  
  /**
   * @return the "--spec_literals" setting.
   */
  public /*@ pure @*/ boolean isSpecLiteralsSet() {
    return my_spec_literals;
  }
  
  // clean setting
  
  /**
   * Sets the "--clean" option.
   * 
   * @param the_clean The new setting.
   */
  public void setClean(final boolean the_clean) {
    my_clean = the_clean;
  }
  
  /**
   * @return the "--clean" setting.
   */
  public /*@ pure @*/ boolean isCleanSet() {
    return my_clean;
  }
  
  // prune setting
  
  /**
   * Sets the "--prune" option.
   * 
   * @param the_prune The new setting.
   */
  public void setPrune(final boolean the_prune) {
    my_prune = the_prune;
  }
  
  /**
   * @return the "--prune" setting.
   */
  public /*@ pure @*/ boolean isPruneSet() {
    return my_prune;
  }
  
  // no_gen setting
  
  /**
   * Sets the "--no_gen" option.
   * 
   * @param the_no_gen The new setting.
   */
  public void setNoGen(final boolean the_no_gen) {
    my_no_gen = the_no_gen;
  }
  
  /**
   * @return the "--no_gen" setting.
   */
  public /*@ pure @*/ boolean isNoGenSet() {
    return my_no_gen;
  }
  
  // dry_run setting
  
  /**
   * Sets the "--dry_run" option.
   * 
   * @param the_dry_run The new setting.
   */
  public void setDryRun(final boolean the_dry_run) {
    my_dry_run = the_dry_run;
  }
  
  /**
   * @return the "--dry_run" setting.
   */
  public /*@ pure @*/ boolean isDryRunSet() {
    return my_dry_run;
  }
  
  // verbose setting
  
  /**
   * Sets the "--verbose" option.
   * 
   * @param the_verbose The new setting.
   */
  public void setVerbose(final boolean the_verbose) {
    my_verbose = the_verbose;
  }
  
  /**
   * @return the "--verbose" setting.
   */
  public /*@ pure @*/ boolean isVerboseSet() {
    return my_verbose;
  }
}

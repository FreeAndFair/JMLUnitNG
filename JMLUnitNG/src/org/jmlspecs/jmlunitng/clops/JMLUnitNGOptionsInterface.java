package org.jmlspecs.jmlunitng.clops;

import java.util.List;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface JMLUnitNGOptionsInterface {


// Option Destination. 
// Aliases: [-d, --dest]

  /**
   * @return true if the option Destination has been used
   * in the command line.
   */
  boolean isDestinationSet();

  /**
   * Get the value of {@code Option} Destination.
   * @return the value of the option Destination if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getDestination();
  

// Option TestPackage. 
// Aliases: [--test-package]

  /**
   * @return true if the option TestPackage has been used
   * in the command line.
   */
  boolean isTestPackageSet();

  /**
   * Get the value of {@code Option} TestPackage.
   * @return the value of the option TestPackage if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getTestPackage();
  

// Option RACVersion. 
// Aliases: [--rac-version]

  /**
   * @return true if the option RACVersion has been used
   * in the command line.
   */
  boolean isRACVersionSet();

  /**
   * Get the value of {@code Option} RACVersion.
   * @return the value of the option RACVersion if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getRACVersion();
  

// Option Files. 
// Aliases: []

  /**
   * @return true if the option Files has been used
   * in the command line.
   */
  boolean isFilesSet();

  /**
   * Get the value of {@code Option} Files.
   * @return the value of the option Files if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<java.io.File> getFiles();
  

// Option Reflection. 
// Aliases: [-r, --reflection]

  /**
   * @return true if the option Reflection has been used
   * in the command line.
   */
  boolean isReflectionSet();

  /**
   * Get the value of {@code Option} Reflection.
   * @return the value of the option Reflection if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getReflection();
  

// Option Help. 
// Aliases: [-h, --help]

  /**
   * @return true if the option Help has been used
   * in the command line.
   */
  boolean isHelpSet();

  /**
   * Get the value of {@code Option} Help.
   * @return the value of the option Help if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getHelp();
  

// Option Deprecation. 
// Aliases: [-d, --deprecation]

  /**
   * @return true if the option Deprecation has been used
   * in the command line.
   */
  boolean isDeprecationSet();

  /**
   * Get the value of {@code Option} Deprecation.
   * @return the value of the option Deprecation if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getDeprecation();
  

// Option Verbose. 
// Aliases: [-v, --verbose]

  /**
   * @return true if the option Verbose has been used
   * in the command line.
   */
  boolean isVerboseSet();

  /**
   * Get the value of {@code Option} Verbose.
   * @return the value of the option Verbose if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getVerbose();
  

// Option Inherited. 
// Aliases: [-i, --inherited]

  /**
   * @return true if the option Inherited has been used
   * in the command line.
   */
  boolean isInheritedSet();

  /**
   * Get the value of {@code Option} Inherited.
   * @return the value of the option Inherited if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getInherited();
  

// Option Public. 
// Aliases: [--public]

  /**
   * @return true if the option Public has been used
   * in the command line.
   */
  boolean isPublicSet();

  /**
   * Get the value of {@code Option} Public.
   * @return the value of the option Public if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPublic();
  

// Option Protected. 
// Aliases: [--protected]

  /**
   * @return true if the option Protected has been used
   * in the command line.
   */
  boolean isProtectedSet();

  /**
   * Get the value of {@code Option} Protected.
   * @return the value of the option Protected if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getProtected();
  

// Option Package. 
// Aliases: [--package]

  /**
   * @return true if the option Package has been used
   * in the command line.
   */
  boolean isPackageSet();

  /**
   * Get the value of {@code Option} Package.
   * @return the value of the option Package if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPackage();
  

// Option Clean. 
// Aliases: [--clean]

  /**
   * @return true if the option Clean has been used
   * in the command line.
   */
  boolean isCleanSet();

  /**
   * Get the value of {@code Option} Clean.
   * @return the value of the option Clean if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getClean();
  

// Option Prune. 
// Aliases: [--prune]

  /**
   * @return true if the option Prune has been used
   * in the command line.
   */
  boolean isPruneSet();

  /**
   * Get the value of {@code Option} Prune.
   * @return the value of the option Prune if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPrune();
  

// Option Classpath. 
// Aliases: [-cp, --classpath]

  /**
   * @return true if the option Classpath has been used
   * in the command line.
   */
  boolean isClasspathSet();

  /**
   * Get the value of {@code Option} Classpath.
   * @return the value of the option Classpath if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<java.io.File> getClasspath();
  

// Option Specspath. 
// Aliases: [-sp, --specspath]

  /**
   * @return true if the option Specspath has been used
   * in the command line.
   */
  boolean isSpecspathSet();

  /**
   * Get the value of {@code Option} Specspath.
   * @return the value of the option Specspath if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<java.io.File> getSpecspath();
  
}

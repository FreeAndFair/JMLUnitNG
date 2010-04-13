
package org.jmlspecs.openjmlunit.clops;

import java.util.List;

/**
 * The interface used to handle the options on the user side.
 * 
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface CmdOptionsOptionsInterface
{

  // Option Destination.
  // Aliases: [-d, --dest]

  /**
   * @return true if the option Destination has been used in the command line.
   */
  boolean isDestinationSet();

  /**
   * Get the value of {@code Option} Destination.
   * 
   * @return the value of the option Destination if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  String getDestination();

  // Option List.
  // Aliases: [-f, --files]

  /**
   * @return true if the option List has been used in the command line.
   */
  boolean isListSet();

  /**
   * Get the value of {@code Option} List.
   * 
   * @return the value of the option List if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  List<java.io.File> getList();

  // Option Help.
  // Aliases: [-h, --help]

  /**
   * @return true if the option Help has been used in the command line.
   */
  boolean isHelpSet();

  /**
   * Get the value of {@code Option} Help.
   * 
   * @return the value of the option Help if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getHelp();

  // Option Package.
  // Aliases: [-p, --package]

  /**
   * @return true if the option Package has been used in the command line.
   */
  boolean isPackageSet();

  /**
   * Get the value of {@code Option} Package.
   * 
   * @return the value of the option Package if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  List<java.io.File> getPackage();

  // Option Universes.
  // Aliases: [-u, --universes]

  /**
   * @return true if the option Universes has been used in the command line.
   */
  boolean isUniversesSet();

  /**
   * Get the value of {@code Option} Universes.
   * 
   * @return the value of the option Universes if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getUniverses();

  // Option Deprication.
  // Aliases: [-dep, --deprication]

  /**
   * @return true if the option Deprication has been used in the command line.
   */
  boolean isDepricationSet();

  /**
   * Get the value of {@code Option} Deprication.
   * 
   * @return the value of the option Deprication if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getDeprication();

  // Option SafeMath.
  // Aliases: [-s, --safemath]

  /**
   * @return true if the option SafeMath has been used in the command line.
   */
  boolean isSafeMathSet();

  /**
   * Get the value of {@code Option} SafeMath.
   * 
   * @return the value of the option SafeMath if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getSafeMath();

  // Option Verbose.
  // Aliases: [-v, --verbose]

  /**
   * @return true if the option Verbose has been used in the command line.
   */
  boolean isVerboseSet();

  /**
   * Get the value of {@code Option} Verbose.
   * 
   * @return the value of the option Verbose if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getVerbose();

  // Option Universesx.
  // Aliases: [-E]

  /**
   * @return true if the option Universesx has been used in the command line.
   */
  boolean isUniversesxSet();

  /**
   * Get the value of {@code Option} Universesx.
   * 
   * @return the value of the option Universesx if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  String getUniversesx();

  // Option Inherited.
  // Aliases: [-inherited]

  /**
   * @return true if the option Inherited has been used in the command line.
   */
  boolean isInheritedSet();

  /**
   * Get the value of {@code Option} Inherited.
   * 
   * @return the value of the option Inherited if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getInherited();

  // Option Public.
  // Aliases: [-public]

  /**
   * @return true if the option Public has been used in the command line.
   */
  boolean isPublicSet();

  /**
   * Get the value of {@code Option} Public.
   * 
   * @return the value of the option Public if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getPublic();

  // Option Protected.
  // Aliases: [-protected]

  /**
   * @return true if the option Protected has been used in the command line.
   */
  boolean isProtectedSet();

  /**
   * Get the value of {@code Option} Protected.
   * 
   * @return the value of the option Protected if it has been set using the
   *         arguments. Throws an {@code IllegalStateException} otherwise.
   */
  boolean getProtected();

}

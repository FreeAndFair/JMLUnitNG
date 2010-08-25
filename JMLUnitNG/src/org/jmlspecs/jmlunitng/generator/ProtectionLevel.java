/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "April 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.jmlunitng.generator;

/**
 * An enumeration of Java protection levels.
 * @author Jonathan Hogins
 * @version April 2010
 */
public enum ProtectionLevel {
  /** The public protection level. **/
  PUBLIC,
  /** The protected protection level. **/
  PROTECTED,
  /** No protection level specified. **/
  NO_LEVEL,
  /** The private protection level. **/
  PRIVATE;
  
  /**
   * @param the_level The other level.
   * @return Is this protection level stronger than the_level?
   */
  public boolean strongerThan(final ProtectionLevel the_level)
  {
    return ordinal() > the_level.ordinal();
  }
  
  /**
   * @param the_level The other level.
   * @return Is this protection level weaker than or equal to the_level?
   */
  public boolean weakerThanOrEqualTo(final ProtectionLevel the_level)
  {
    return ordinal() <= the_level.ordinal();
  }
  
  /**
   * @return the String representation of this protection level
   */
  public String toString() {
    String result = this.name().toLowerCase();
    if (this == NO_LEVEL) {
      result = "(package)";
    }
    return result;
  }
}

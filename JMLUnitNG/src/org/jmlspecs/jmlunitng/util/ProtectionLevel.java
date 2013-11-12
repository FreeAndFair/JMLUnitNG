/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.util;

/**
 * An enumeration of Java protection levels.
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version July 2011
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
  public boolean strongerThan(final ProtectionLevel the_level) {
    return ordinal() > the_level.ordinal();
  }
  
  /**
   * @param the_level The other level.
   * @return Is this protection level weaker than or equal to the_level?
   */
  public boolean weakerThanOrEqualTo(final ProtectionLevel the_level) {
    return ordinal() <= the_level.ordinal();
  }
  
  /**
   * @return the String representation of this protection level
   */
  public String toString() {
    String result = this.name().toLowerCase();
    if (this == NO_LEVEL) {
      result = "package-protected";
    }
    return result;
  }
}

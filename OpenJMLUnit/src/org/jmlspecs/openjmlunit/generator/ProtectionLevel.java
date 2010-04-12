/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * @module "OpenJML"
 * @creation_date "April 2010"
 * @last_updated_date "April 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

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
  /** The private protection level. **/
  PRIVATE,
  /** No protection level specified. **/
  NO_LEVEL
}

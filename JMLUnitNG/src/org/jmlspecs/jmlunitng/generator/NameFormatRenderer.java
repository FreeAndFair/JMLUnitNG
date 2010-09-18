/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.generator;

import org.antlr.stringtemplate.AttributeRenderer;

/**
 * A renderer for StringTemplates that renders class and method
 * names appropriately for use as/in package and class names
 * in code generation.
 * 
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public class NameFormatRenderer implements AttributeRenderer {
  /**
   * {@inheritDoc}
   */
  @Override
  public String toString(final Object the_obj) {
    String result = null; 
    
    if (the_obj != null) {
      result = the_obj.toString();
    }
    
    return result;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public String toString(final Object the_obj,
                         final String the_format) {
    String result = null; 
    
    if (the_obj != null) {
      switch (decodeFormat(the_format)) {
        case PACKAGE:
          // convert to all lower case with underscores
          break;
          
        case CLASS:
          // convert to CamelCase
          break;
          
        default:
          throw new IllegalArgumentException("Unsupported format");
      }
    }
    
    return result;
  }

  /**
   * Decodes the format string into an enum value for use in 
   * a switch.
   * 
   * @param the_format The format string.
   * @return the resulting enum value.
   */
  private Format decodeFormat(final String the_format) {
    Format result;
    
    if ("package".equals(the_format)) {
      result = Format.PACKAGE;
    } else if ("class".equals(the_format)) {
      result = Format.CLASS;
    } else {
      result = Format.UNKNOWN;
    }
    
    return result;
  }
  
  /**
   * A private enumeration of the format types.
   * 
   * @author Daniel M. Zimmerman
   * @version August 2010
   */
  private enum Format {
    /**
     * The "package" type. 
     */
    PACKAGE,
    
    /**
     * The "class" type.
     */
    CLASS,
    
    /**
     * The "unknown" type.
     */
    UNKNOWN;
  }
}

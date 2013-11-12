/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.util;

import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.jmlunitng.JMLUnitNGError;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;
import org.stringtemplate.v4.compiler.STException;

/**
 * Handles loading of StringTemplate groups.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public final class StringTemplateUtil {
  /**
   * The path to all templates.
   */
  // no need for cross-platform file separators because ST handles them properly
  private static final String TEMPLATE_PATH = "org/jmlspecs/jmlunitng/templates/";
  
  /**
   * The cache of already-loaded templates.
   */
  private static final Map<String, STGroup> LOADED = new HashMap<String, STGroup>();
  
  /**
   * Private constructor to prevent instantiation of this class.
   */
  private StringTemplateUtil() {
    // do nothing
  }
  
  /**
   * Gets one of our StringTemplate groups.
   * 
   * @param the_name The name of the group (e.g., "shared_java").
   * @return The group.
   */
  public static synchronized STGroup load(final String the_name) {
    STGroup result = LOADED.get(the_name);
    if (result == null) {
      try {
        result = new STGroupFile(TEMPLATE_PATH + the_name + ".stg");
        LOADED.put(the_name, result);
      } catch (final STException e) {
        throw new JMLUnitNGError("Unable to load template " + the_name, e);
      }
    } 
    return result;
  }
}

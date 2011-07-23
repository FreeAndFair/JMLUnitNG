/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.util;

import java.io.File;

import org.antlr.stringtemplate.CommonGroupLoader;
import org.antlr.stringtemplate.StringTemplateGroup;
import org.antlr.stringtemplate.StringTemplateGroupLoader;

/**
 * Handles initialization of StringTemplate.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public final class StringTemplateUtil {
  /**
   * The path to all templates.
   */
  private static final String TEMPLATE_PATH = 
    "org/jmlspecs/jmlunitng/templates:org" + File.separator + 
    "jmlspecs" + File.separator + "jmlunitng" + File.separator + 
    "templates";
  
  /**
   * A flag indicating whether StringTemplate has been initialized.
   */
  private static boolean my_initialized;
  
  /**
   * Private constructor to prevent instantiation of this class.
   */
  private StringTemplateUtil() {
    // do nothing
  }

  /**
   * Initialize StringTemplate if it is not already initialized!
   */
  //@ ensures isInitialized();
  public static synchronized void initialize() {
    if (!my_initialized) {
      final StringTemplateGroupLoader loader =
        new CommonGroupLoader(TEMPLATE_PATH, null);
      StringTemplateGroup.registerGroupLoader(loader);

      my_initialized = true;
    }
  }
  
  /**
   * @return Has StringTemplate been initialized?
   */
  //@ constraint \old(isInitialized()) ==> isInitialized();
  public static synchronized boolean isInitialized() {
    return my_initialized;
  }
}

/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @author Jonathan Hogins
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
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
  private static final String TEMPLATE_PATH = "res" + File.separator + "templates";
  
  /**
   * Has StringTemplate been instantiated?
   */
  private static boolean my_initialized;
  
  /**
   * Private constructor to prevent initialization.
   */
  private StringTemplateUtil() {
  }

  /**
   * Initialize StringTemplates if it not already initialized.
   */
  //@ ensures isInitialized();
  public synchronized static void initialize() {
    if (!my_initialized) {
      final StringTemplateGroupLoader loader =
        new CommonGroupLoader(TEMPLATE_PATH, null);
      StringTemplateGroup.registerGroupLoader(loader);
      my_initialized = true;
    }
  }
  /**
   * Returns true if StringTemplate has been initialized with 
   * StringTemplateUtil.initialize().
   * @return True if initialized. False if not.
   */
  //@ constraint \old(isInitialized()) ==> isInitialized();
  public synchronized static boolean isInitialized() {
    return my_initialized;
  }
}

/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

import java.io.File;
import java.io.IOException;
import java.util.List;

import com.sun.tools.javac.tree.JCTree;

/**
 * Factory class that generates CLASS_INFO and METHOD_INFO objects.
 * 
 * @author Daniel M. Zimmerman
 * @version March 2010
 */
public final class InfoFactory {
  /**
   * Private constructor to prevent initialization.
   */
  private InfoFactory() {
  }

  /**
   * Creates a ClassInfo object for the given java source File.
   * 
   * @param the_file The File object to parse.
   * @return A ClassInfo object representing the class defined in the_file.
   * @throws IOException An IO error occurred during file parsing.
   */
  public static ClassInfo createClassInfo(final File the_file) throws IOException {
    //TODO: Implement.
    return null;
  }

  /**
   * Creates a ClassInfo object for the given JCTree.
   * 
   * @param the_tree The JCTree to parse for a class.
   * @return A ClassInfo object representing the class.
   */
  public static ClassInfo createClassInfo(final JCTree the_tree) {
    //TODO: Implement.
    return null;
  }

  /**
   * Creates a ClassInfo object for the given Class.
   * 
   * @param the_class The Class generate a ClassInfo object for.
   * @return A ClassInfo object representing the class.
   */
  public static ClassInfo createClassInfo(final Class<?> the_class) {
    //TODO: Implement.
    return null;
  }

  //  "Create a CLASS_INFO object for the given Class!",
  //  "Create a List<METHOD_INFO> objects for the given JCTree!"

  /**
   * Creates a MethodInfo object for each method in the given JCTree and returns
   * a list of them.
   * 
   * @param the_tree The JCTree to parse for methods.
   * @return A List<MethodInfo> representing the methods in the tree.
   */
  public static List<MethodInfo> createMethodInfos(final JCTree the_tree) {
    //TODO: Implement.
    return null;
  }

}

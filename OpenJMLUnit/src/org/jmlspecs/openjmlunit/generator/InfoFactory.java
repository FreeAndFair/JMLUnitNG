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

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.lang.model.element.Modifier;

import org.jmlspecs.openjml.API;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeScanner;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;

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
   * Creates a ClassInfo object for the given JCTree.
   * 
   * @param the_tree The JCTree to parse for a class.
   * @return A ClassInfo object representing the class.
   */
  public static ClassInfo createClassInfo(final JCTree the_tree) {
    final ClassInfoParser parser = new ClassInfoParser();
    the_tree.accept(parser);
    return parser.getClassInfo();
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
    final ClassInfoParser parser = new ClassInfoParser();
    the_tree.accept(parser);
    return parser.getMethodInfos();
  }

  /**
   * JCTree scanner that records relevant information on the class and methods
   * scanned.
   * 
   * @author Jon
   */
  private static class ClassInfoParser extends TreeScanner {
    /**
     * The parsed ClassInfo object.
     */
    private ClassInfo my_class_info;
    /**
     * The MethodInfo objects parsed.
     */
    private List<MethodInfo> my_method_infos;

    /**
     * Creates a new ClassInfoParser.
     */
    public ClassInfoParser() {
      my_class_info = null;
      my_method_infos = new LinkedList<MethodInfo>();
    }

    /**
     * Overridden method. Extracts all class data except method data.
     * 
     * @param the_tree The class declaration node.
     */
    //@ ensures my_class_info != null
    public void visitClassDef(final JCClassDecl the_tree) {
      if (my_class_info != null) {
        //TODO: Implement
        System.err.println("WARNING: Inner classes not yet handled.");
        super.visitClassDef(the_tree);
      }
      final String name = the_tree.name.toString();
      final Set<Modifier> flags = the_tree.getModifiers().getFlags();
      ProtectionLevel level = null;
      if (flags.contains(Modifier.PUBLIC)) {
        level = ProtectionLevel.PUBLIC;
      } else if (flags.contains(Modifier.PROTECTED)) {
        level = ProtectionLevel.PROTECTED;
      } else if (flags.contains(Modifier.PRIVATE)) {
        level = ProtectionLevel.PRIVATE;
      }
      final boolean is_abstract = flags.contains(Modifier.ABSTRACT);
      final ClassInfo parent = null;
      if (the_tree.extending != null && the_tree.extending instanceof JCIdent) {
        //TODO: Implement
        System.err.println("WARNING: \"extends\" expression not yet handled.");
      }
      my_class_info = new ClassInfo(name, level, is_abstract, my_method_infos, parent);
      super.visitClassDef(the_tree);
    }

    /**
     * Overridden method. Extracts a MethodInfo object from the method data and
     * adds it to the list.
     * 
     * @param the_tree The method declaration node.
     */
    //@ ensures \old my_method_infos.size() == my_method_infos.size() - 1;
    public void visitMethodDef(final JCMethodDecl the_tree) {
      final String name = the_tree.name.toString();
      final Set<Modifier> flags = the_tree.getModifiers().getFlags();
      ProtectionLevel level = null;
      if (flags.contains(Modifier.PUBLIC)) {
        level = ProtectionLevel.PUBLIC;
      } else if (flags.contains(Modifier.PROTECTED)) {
        level = ProtectionLevel.PROTECTED;
      } else if (flags.contains(Modifier.PRIVATE)) {
        level = ProtectionLevel.PRIVATE;
      }
      final String return_type;
      if (the_tree.restype == null) {
        return_type = my_class_info.getName();
      } else {
        return_type = the_tree.restype.type.toString();
      }
      final boolean is_constructor =
        "<init>".equals(the_tree.getName()) && return_type.equals(my_class_info.getName());
      final boolean is_static = flags.contains(Modifier.STATIC);
      final List<String> parameters = new LinkedList<String>();
      for (JCVariableDecl var : the_tree.params) {
        parameters.add(var.vartype.type.toString());
      }
      my_method_infos.add(new MethodInfo(name, my_class_info, null, level, parameters,
                                         return_type, is_constructor, is_static));
      super.visitMethodDef(the_tree);
    }
    
    /**
     * Returns the ClassInfo object parsed by this visitor. Returns null if a tree containing a
     * JCClassDef node has not been parsed yet.
     * 
     * @return The ClassInfo for the parsed file.
     */
    public ClassInfo getClassInfo() {
      return my_class_info;
    }

    /**
     * Returns the list of MethodInfo objects generated while parsing the tree.
     * 
     * @return The list of parsed MethodInfo objects.
     */
    public List<MethodInfo> getMethodInfos() {
      return my_method_infos;
    }

  }

}

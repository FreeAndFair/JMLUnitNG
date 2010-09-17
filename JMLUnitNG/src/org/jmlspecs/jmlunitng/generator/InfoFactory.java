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

package org.jmlspecs.jmlunitng.generator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.Modifier;

import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.TreeScanner;

/**
 * Factory class that generates ClassInfo and MethodInfo objects.
 * 
 * @author Daniel M. Zimmerman
 * @author Jonathan Hogins
 * @version September 2010
 */
public final class InfoFactory {
  /**
   * Cache of already created ClassInfo objects. 
   */
  private static final Map<String, ClassInfo> CLASS_CACHE = 
    new HashMap<String, ClassInfo>();

  /**
   * Private constructor to prevent initialization.
   */
  private InfoFactory() {
  }

  /**
   * Returns the ClassInfo object for the given JCTree. Returns the cached
   * version if one exists for the class's qualified name.
   * 
   * @param the_tree The JCTree to parse for a class.
   * @return A ClassInfo object representing the class.
   */
  public static ClassInfo getClassInfo(final JCTree the_tree) {
    final ClassInfoParser parser = new ClassInfoParser();
    the_tree.accept(parser);
    return parser.getClassInfo();
  }

  /**
   * Creates a ClassInfo object for the given ClassSymbol. Returns a cached
   * version if one exists for the class's qualified name.
   * 
   * @param the_class The Class generate a ClassInfo object for.
   * @return A ClassInfo object representing the class.
   */
  public synchronized static ClassInfo getClassInfo(final ClassSymbol the_class) {
    if (CLASS_CACHE.containsKey(the_class.getQualifiedName().toString())) {
      return CLASS_CACHE.get(the_class.getQualifiedName().toString());
    }
    final String name = the_class.getQualifiedName().toString();
    final Set<Modifier> flags = the_class.getModifiers();
    final boolean is_abstract = flags.contains(Modifier.ABSTRACT);
    ClassInfo parent = null;
    //check for instanceof. Returns a NoType instance if no superclass exists
    if (the_class.getSuperclass() instanceof ClassType) {
      parent = getClassInfo((ClassSymbol) the_class.getSuperclass().tsym);
    }
    final Set<MethodInfo> method_infos = new HashSet<MethodInfo>();
    final Scope members = the_class.members();
    final ClassInfo result =
        new ClassInfo(name, getLevel(flags), is_abstract, parent);
    // ensure this ClassInfo object is cached before creating methods
    CLASS_CACHE.put(name, result);
    // add methods after ClassInfo creation.
    for (Scope.Entry e = members.elems; e != null; e = e.sibling) {
      if (e.sym != null && (e.sym.getKind().equals(ElementKind.METHOD) || 
          e.sym.getKind().equals(ElementKind.CONSTRUCTOR))) {
        method_infos.add(createMethodInfo((MethodSymbol) e.sym, result));
      }
    }
    // add inherited methods from the parent class
    if (parent != null)
    {
      final Set<MethodInfo> parent_methods = 
        new HashSet<MethodInfo>(parent.getMethods());
      // we do not inherit methods that were already overridden by the parent class
      parent_methods.removeAll(parent.getOverriddenMethods());
      for (MethodInfo pm : parent_methods)
      {
        if (!pm.isConstructor() && !pm.isStatic() &&
            !pm.getProtectionLevel().equals(ProtectionLevel.PRIVATE))
        {
          // we do not inherit constructors or static/private methods
          boolean duplicate = false;
          for (MethodInfo m : method_infos)
          {
            duplicate = duplicate || 
                        (m.getName().equals(pm.getName()) &&
                         m.getParameters().equals(pm.getParameters()));
          }
          if (!duplicate)
          {
            method_infos.add(new MethodInfo(pm.getName(), result, pm.getDeclaringClass(),
                                            pm.getProtectionLevel(), pm.getParameters(),
                                            pm.getReturnType(), false, false,
                                            pm.isDeprecated()));
          }
        }
      }
    }
    result.initializeMethods(method_infos);
    return result;
  }

  // "Create a CLASS_INFO object for the given Class!",
  // "Create a List<METHOD_INFO> objects for the given JCTree!"

  /**
   * Creates a MethodInfo object for each method in the given JCTree and returns
   * a list of them.
   * 
   * @param the_tree The JCTree to parse for methods.
   * @return A List<MethodInfo> representing the methods in the tree.
   */
  public static List<MethodInfo> createMethodInfos(final JCTree the_tree) {
    final MethodInfoParser parser = new MethodInfoParser();
    the_tree.accept(parser);
    return parser.getMethodInfos();
  }

  /**
   * Creates a MethodInfo object for the given MethodSymbol enclosed in the
   * given ClassInfo.
   * 
   * @param the_sym The MethodSymbol to create a MethodInfo object for.
   * @param the_parent_class The ClassInfo that contains this MethodInfo.
   */
  /*@ ensures (\forall String s; \result.getParameterTypes().contains(s);
    @             (\exists VarSymbol v; the_sym.params.contains(v); 
    @                 s.equals(v.getSimpleName().toString()))) &&
    @         the_parent_class != null ==> \result.getParentClass() == the_parent_class &&
    @         the_parent_class == null ==> \result.getParentClass() == \result.getDeclaringClass() &&
    @         \result.getDeclaringClass().getFullyQualifiedName()
    @             .equals(the_sym.getEnclosingElement().getQualifiedName().toString()) &&
    @         \result.getProtectionLevel() == getLevel(the_sym.getModifiers()) &&
    @         \result.isConstructor() == the_sym.isConstructor() &&
    @         \result.isStatic() == the_sym.isStatic();
   */
  public static MethodInfo createMethodInfo(final MethodSymbol the_sym,
                                            final/*@ nullable */ClassInfo the_parent_class) {
    final List<ParameterInfo> params = new ArrayList<ParameterInfo>(the_sym.getParameters().size());
    for (VarSymbol v : the_sym.params) {
      params.add(createParameterInfo(v));
    }
    ClassInfo declaring_class = the_parent_class;
    if (the_sym.getEnclosingElement() instanceof ClassSymbol) {
      final ClassSymbol parent = (ClassSymbol) the_sym.getEnclosingElement();
      if (the_parent_class == null ||
          !parent.getQualifiedName().toString().equals(the_parent_class.getShortName())) {
        declaring_class = getClassInfo(parent);
      }
    }
    ClassInfo parent_class = the_parent_class;
    if (parent_class == null) {
      parent_class = declaring_class;
    }
    final ProtectionLevel level = getLevel(the_sym.getModifiers());
    String name = the_sym.getSimpleName().toString();
    
    // is the method a constructor?
    if ("<init>".equals(name)) {
      name = the_parent_class.getShortName();
    }
    
    // is the method deprecated? this is crude but functional
    boolean deprecated = false;
    final List<Attribute.Compound> annotations = the_sym.getAnnotationMirrors();
    for (Attribute.Compound a : annotations) {
      deprecated |= "@java.lang.Deprecated".equals(a.toString());
    }
    
    return new MethodInfo(name, parent_class, declaring_class,
                          level, params, new TypeInfo(the_sym.getReturnType().toString()),
                          the_sym.isConstructor(), the_sym.isStatic(), deprecated);
  }
  
  /**
   * Returns a ParameterInfo object representing the given VarSymbol.
   * @param the_var_sym The VarSymbol to translate into a ParameterInfo object.
   */
  /*@ ensures \result.getParameterName().equals(the_var_sym.name.toString()) &&
    @         \result.isArray() <==> the_var_sym.type.tag == TypeTags.ARRAY;
   */
  public static ParameterInfo createParameterInfo(final VarSymbol the_var_sym) {
    Type t = the_var_sym.type;
    boolean is_array = false;
    if (t.tag == TypeTags.ARRAY) {
      is_array = true;
      t = ((ArrayType)t).getComponentType();
    }
    //remove any generic elements
    while (t.tag == TypeTags.TYPEVAR) {
      t = t.getUpperBound().tsym.asType();
    }
    return new ParameterInfo(t.toString(), the_var_sym.name.toString(), is_array);
  }

  /**
   * Returns the protection level present in the given set of Modifiers. Returns
   * null if there are no protection level modifiers (PUBLIC, PROTECTED,
   * PRIVATE) in the given set.
   * 
   * @param the_mods The Set<Modifier> from which to extract the protection
   *          level
   */
  /*@ ensures \result.equals(ProtectionLevel.PUBLIC) ==> the_mods.contains(Modifier.PUBLIC) &&
    @         \result.equals(ProtectionLevel.PROTECTED) ==> 
    @           (!the_mods.contains(Modifier.PUBLIC)  && the_mods.contains(Modifier.PROTECTED)) &&  
    @         \result.equals(ProtectionLevel.PRIVATE) ==> (!the_mods.contains(Modifier.PUBLIC) &&
    @            !the_mods.contains(Modifier.PROTECTED) && the_mods.contains(Modifier.PRIVATE)) && 
    @         \result.equals(ProtectionLevel.NO_LEVEL) ==> (!the_mods.contains(Modifier.PUBLIC) &&
    @            !the_mods.contains(Modifier.PROTECTED) && !the_mods.contains(Modifier.PRIVATE));
   */
  private static ProtectionLevel getLevel(final Set<Modifier> the_mods) {

    ProtectionLevel level = ProtectionLevel.NO_LEVEL;
    if (the_mods.contains(Modifier.PUBLIC)) {
      level = ProtectionLevel.PUBLIC;
    } else if (the_mods.contains(Modifier.PROTECTED)) {
      level = ProtectionLevel.PROTECTED;
    } else if (the_mods.contains(Modifier.PRIVATE)) {
      level = ProtectionLevel.PRIVATE;
    }
    return level;
  }

  /**
   * JCTree scanner that records relevant information on the class and methods
   * scanned.
   * 
   * @author Jonathan Hogins
   */
  private static class ClassInfoParser extends TreeScanner {
    /**
     * The parsed ClassInfo object.
     */
    private ClassInfo my_class_info;

    /**
     * Overridden method. Extracts all class data except method data.
     * 
     * @param the_tree The class declaration node.
     */
    // @ ensures my_class_info != null
    public void visitClassDef(final JCClassDecl the_tree) {
      my_class_info = InfoFactory.getClassInfo(the_tree.sym);
    }

    /**
     * Returns the ClassInfo object parsed by this visitor. Returns null if a
     * tree containing a JCClassDef node has not been parsed yet.
     * 
     * @return The ClassInfo for the parsed file.
     */
    public ClassInfo getClassInfo() {
      return my_class_info;
    }
  }

  /**
   * JCTree scanner that records MethodInfo objects for the visited method
   * nodes. The MethodInfo objects' parent class will equal the first class
   * definition encountered in the tree. If there are not class definitions in
   * the tree, the parent class is the class in which the method is defined.
   * 
   * @author Jonathan Hogins
   */
  private static class MethodInfoParser extends TreeScanner {
    /**
     * The parsed ClassInfo object.
     */
    private ClassInfo my_class_info;
    
    /**
     * The MethodInfo objects parsed.
     */
    private final List<MethodInfo> my_method_infos;

    /**
     * Creates a new MethodInfoParser.
     */
    public MethodInfoParser() {
      super();
      my_method_infos = new LinkedList<MethodInfo>();
    }

    /**
     * Overridden method. Extracts all class data except method data.
     * 
     * @param the_tree The class declaration node.
     */
    // @ ensures my_class_info != null
    public void visitClassDef(final JCClassDecl the_tree) {
      my_class_info = InfoFactory.getClassInfo(the_tree.sym);
      super.visitClassDef(the_tree);
    }

    /**
     * Overridden method. Extracts a MethodInfo object from the method data and
     * adds it to the list.
     * 
     * @param the_tree The method declaration node.
     */
    // @ ensures \old my_method_infos.size() == my_method_infos.size() - 1;
    public void visitMethodDef(final JCMethodDecl the_tree) {
      my_method_infos.add(createMethodInfo(the_tree.sym, my_class_info));
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

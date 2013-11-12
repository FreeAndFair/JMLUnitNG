/*
 * JMLUnitNG 
 * Copyright (C) 2010-13
 */

package org.jmlspecs.jmlunitng.util;

import java.util.Comparator;

import org.jmlspecs.jmlunitng.generator.ClassInfo;

/**
 * A comparator that considers classes lower in the inheritance hierarchy
 * to be "less than" classes higher in the inheritance hierarchy. This
 * comparator implements a partial order.
 * 
 * @author Daniel M. Zimmerman
 * @version July 2011
 */
public class InheritanceComparator implements Comparator<ClassInfo> {
  
  /**
   * Compare two classes to determine which is higher in the inheritance
   * hierarchy.
   * 
   * @param class_1 The first class.
   * @param class_2 The second class.
   * @return -1 if class_1 is lower than class_2 in the hierarchy, 1 if
   * class_2 is lower than class_1 in the hierarchy, and 0 if they have no
   * ordering with respect to each other. 
   */
  public int compare(final ClassInfo class_1, final ClassInfo class_2) {
    int result = 0;
    if (!class_1.equals(class_2)) {
      // figure out which class is higher on the inheritance hierarchy
      // if they are unrelated, they are considered equal
      
      ClassInfo parent = class_1.getParent();
      while (parent != null) {
        if (parent.equals(class_2)) {
          result = -1; 
          break;
        }
        parent = parent.getParent();
      }
      parent = class_2.getParent();
      while (parent != null) {
        if (parent.equals(class_1)) {
          result = 1;
          break;
        }
        parent = parent.getParent();
      }
    }
    return result;
  }
}

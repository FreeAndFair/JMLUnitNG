/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.util;

import java.io.Serializable;
import java.util.Comparator;

import org.jmlspecs.jmlunitng.generator.ClassInfo;

/**
 * A comparator that considers classes lower in the inheritance hierarchy
 * to be "less than" classes higher in the inheritance hierarchy. This
 * comparator implements a partial order.
 * 
 * @author Daniel M. Zimmerman
 * @version November 2010
 */
public class InheritanceComparator implements Serializable, Comparator<ClassInfo> {
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

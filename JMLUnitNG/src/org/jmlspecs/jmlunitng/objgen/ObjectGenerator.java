/*
 * JMLUnitNG 
 * Copyright (C) 2010-14
 */

package org.jmlspecs.jmlunitng.objgen;

/**
 * A generator for objects of a specific class.
 * 
 * @author Daniel M. Zimmerman
 * @version January 2012
 * @param <T> The type of the generated objects.
 */
public interface ObjectGenerator<T> {
  /**
   * @return a newly-generated object of an appropriate class, or null if
   * such an object cannot be generated.
   */
  Object generate(); 

  /**
   * @return the class of objects generated by this generator.
   */
  Class<?> generatedClass();
}

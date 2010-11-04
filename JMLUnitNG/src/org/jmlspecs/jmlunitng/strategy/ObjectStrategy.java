/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.strategy;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.MultiIterator;
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * The strategy for all non-primitive types. For Enums, it always
 * provides all values of the enum unless the default values are
 * overridden. For other types of object, it attempts to find
 * test data generators for the default values.
 * 
 * @author Jonathan Hogins
 * @author Daniel M. Zimmerman
 * @version November 2010
 */
public abstract class ObjectStrategy implements Strategy {  
  /**
   * The class for which this strategy was made.
   */
  private final Class<?> my_class;
  
  /**
   * The test data class found for the given strategy class.
   */
  private Class<? extends ObjectStrategy> my_test_data;

  /**
   * The enum constants for the given class, if it is an enum type.
   */
  private Object[] my_enum_constants; 
  
  /**
   * Creates a new ObjectStrategy for the given class. If the_reflective flag
   * is true, then default values will be generated reflectively using the 
   * data generator for the class, if it exists, or (in the case of enums) 
   * will be all enum values. If the_reflective flag is false, there will 
   * be no default values.
   * 
   * @param the_class The class to generate the strategy for.
   * @param the_reflective The reflective flag.
   */
  @SuppressWarnings("unchecked")
  public ObjectStrategy(final Class<?> the_class, final boolean the_reflective) {
    my_class = the_class;
    my_test_data = null;
    my_enum_constants = null;
    
    if (the_reflective && the_class.getEnumConstants() == null) {
      // it's not an enum, so let's look for default values
      try {
        final Class<?> data_class = 
          Class.forName(the_class.getName() + "_JML_Data.InstanceStrategy");
        if (ObjectStrategy.class.isAssignableFrom(data_class)) {
          my_test_data = (Class<? extends ObjectStrategy>) data_class;
        }
      } catch (ClassNotFoundException e) {
        my_test_data = null;
      }
    } else if (the_class.getEnumConstants() != null) {
      // it is an enum
      my_enum_constants = the_class.getEnumConstants();
    }
  }

  /**
   * Creates a new ObjectStrategy for the given class. Default values will be
   * generated reflectively by the test data class for the_class if present;
   * for enumerations, all enum constants will be used.
   * 
   * @param the_class The class for which to use test data from.
   */
  public ObjectStrategy(final Class<?> the_class) {
    this(the_class, true);
  }
  
  /**
   * Returns an iterator over the values defined in the class' test data
   * definition if it exists. Otherwise, returns an iterator over
   * DEFAULT_VALUES.
   * 
   * @return An Iterator over default values.
   */
  public RepeatedAccessIterator<?> getDefaultValues() {
    RepeatedAccessIterator<?> result;
    if (my_enum_constants == null && my_test_data == null) {
      // return the default null iterator, since we couldn't get data
      result = new ObjectArrayIterator<Object>(new Object[] { null });
    } else if (my_enum_constants == null) {
      // try to return data generated using reflection
      try {
        result = my_test_data.newInstance().iterator();
      } catch (InstantiationException e) {
        e.printStackTrace();
        result = new ObjectArrayIterator<Object>(new Object[] { null });
      } catch (IllegalAccessException e) {
        e.printStackTrace();
        result = new ObjectArrayIterator<Object>(new Object[] { null });
      }
    } else { // my_enum_constants != null
      // return the enum constants
      result = new ObjectArrayIterator<Object>(my_enum_constants);
    }
       
    return result;
  }
  
  /**
   * A default empty iterator, may be overridden by child classes.
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> getGlobalValues() {
    return new ObjectArrayIterator<Object>
    ((Object[]) Array.newInstance(my_class, 0));
  }

  /**
   * A default empty iterator, may be overridden by child classes.
   * @return An empty iterator.
   */
  public RepeatedAccessIterator<?> getCustomValues() {
    return new ObjectArrayIterator<Object>
    ((Object[]) Array.newInstance(my_class, 0));
  }
  
  /**
   * Returns a RepeatedAccessIterator over all values in the order: default
   * values, custom values, global values.
   * 
   * @return What are all your values?
   */
  @SuppressWarnings("unchecked")
  public RepeatedAccessIterator<?> iterator() {
    final List<RepeatedAccessIterator<?>> iterators = new ArrayList<RepeatedAccessIterator<?>>(3);
    iterators.add(getDefaultValues());
    iterators.add(getCustomValues());
    iterators.add(getGlobalValues());
    return new MultiIterator(iterators);
  }
}

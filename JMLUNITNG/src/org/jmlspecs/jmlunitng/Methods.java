package org.jmlspecs.jmlunitng;

import java.util.ArrayList;
import java.util.List;

/**
 * Class containing the arraylist of methods to be tested.
 * @author Rinkesh Nagmoti
 *@version 1.0
 */
public class Methods
{
  /** List of all methods to be tested.*/
  final List my_methods;
    /** List of all inherited methods to be tested.*/
  final List my_inhtMethods;
  
  /** Constructs the Methods Object.
   * @param the_methods,
   * @param the_inhtMethods
   * */
  public Methods(final List the_methods, final List the_inhtMethods)
  {
    this.my_methods = the_methods;
    this.my_inhtMethods = the_inhtMethods;
  }

  /** Returns the combined list of methods to be tested.
   * @return ArrayList
   */
  public List getCombinedMethodsList()
  {
    final List tempList = null;
    tempList.addAll(my_methods);
    tempList.addAll(my_inhtMethods);

    return tempList;
  }
    //----------------
    //DATA MEMBERS
    //----------------

}

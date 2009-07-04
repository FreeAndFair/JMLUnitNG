package org.jmlspecs.jmlunitng;

import org.multijava.mjc.CMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;

/**
 * Represents method information for the method to be tested.  
 * @author Rinkesh Nagmoti 
 * @version 1.0
 */
public class MethodToBeTested {

  
  /** Represents the return type of the method.*/
  final  CType my_returnType;
  /** Represents the method's modifiers.*/
  final  long my_modifier;
  /** Represents the name of the Method.*/
  final  String my_methodName;
  /** The method's parameters.*/
  final  Parameter[] my_parameters;
  
  /** Constructs the Object to of MethodToBeTested.
   * @param the_mehod
   */
  public MethodToBeTested(final Object the_mth)
  { 
    CMethod the_method = (CMethod)the_mth;
    my_returnType = the_method.returnType();
    my_modifier = the_method.modifiers();
    my_methodName = the_method.getIdent();
    final CSpecializedType[] ts = the_method.parameters();
    my_parameters = new Parameter[ts.length];
    for (int i = 0; i < ts.length; i++)
    {
      my_parameters[i] = new Parameter(ts[i].staticType(), "arg" + (i + 1));
    }
  }

  /** Returns the return type of the method.
   * @return CType
   * */
  public CType getReturnType()
  {
    return my_returnType;
  }
  /** Returns the modifier for the method.
   * @return long
   */
  public long getModifier()
  {
    return my_modifier;
  }
  /** Return the name of the method.
   * @return String 
   */
  public String getName()
  {
    return my_methodName; 
  }
  /** Return the list of Parameters.
   * @return Parameter[]
   */
  public Parameter[] getParaters()
  {
    return my_parameters;
  }
 
}

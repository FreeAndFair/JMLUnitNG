
package org.jmlspecs.jmlunitng;

import org.multijava.mjc.CMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;

/**
 * Represents method information for the method to be tested.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 */
public class MethodToBeTested
{

  /** Represents the return type of the method. */
  private final transient CType my_returnType;
  /** Represents the method's modifiers. */
  private final transient long my_modifier;
  /** Represents the name of the Method. */
  private final transient String my_methodName;
  /** The method's parameters. */
  private final transient Parameter[] my_parameters;

  /**
   * Constructs the Object to of MethodToBeTested.
   * 
   * @param the_mth The Object to be passed as parameter.
   */
  public MethodToBeTested(final Object the_mth)
  {
    final CMethod the_method = (CMethod) the_mth;
    my_returnType = the_method.returnType();
    my_modifier = the_method.modifiers();
    my_methodName = the_method.getIdent();
    final CSpecializedType[] cspType = the_method.parameters();
    my_parameters = new Parameter[cspType.length];
    for (int i = 0; i < cspType.length; i++)
    {
      my_parameters[i] = new Parameter(cspType[i].staticType(), "arg" + (i + 1));
    }
  }

  /**
   * Returns the return type of the method.
   * 
   * @return CType
   * */
  public CType getReturnType()
  {
    return my_returnType;
  }

  /**
   * Returns the modifier for the method.
   * 
   * @return long
   */
  public long getModifier()
  {
    return my_modifier;
  }

  /**
   * Return the name of the method.
   * 
   * @return String
   */
  public String getName()
  {
    return my_methodName;
  }

  /**
   * Return the list of Parameters.
   * 
   * @return Parameter[]
   */
  public Parameter[] getParaters()
  {
    return my_parameters;
  }

}


package org.jmlspecs.openjmlunit.clops;

import ie.ucd.clops.runtime.parser.AbstractSpecificCLParser;
import ie.ucd.clops.runtime.rules.RuleStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;

/**
 * The arguments parser. This is the main entry point for the option's handling.
 * 
 * @author The CLOPS team (kind@ucd.ie)
 */
public class CmdOptionsParser extends AbstractSpecificCLParser
{

  /** The option store used to hold the option's status. */
  private final CmdOptionsOptionStore optionStore;
  /** The store which contains the constraints associated with the options. */
  private final ie.ucd.clops.runtime.rules.RuleStore ruleStore;

  /**
   * Creates a parser to handle the options.
   * 
   * @throws InvalidOptionPropertyValueException if one of the options had an
   *           invalid property attached to it in the CLOPS description file.
   */
  public CmdOptionsParser() throws InvalidOptionPropertyValueException
  {
    optionStore = new CmdOptionsOptionStore();
    ruleStore = new CmdOptionsRuleStore();
  }

  /**
   * Get the {@link OptionStore} containing the option instances for this
   * parser.
   * 
   * @return the option store.
   */
  public CmdOptionsOptionStore getOptionStore()
  {
    return optionStore;
  }

  /**
   * Get the {@link RuleStore} containing the rules for this parser.
   * 
   * @return the option store.
   */
  public RuleStore getRuleStore()
  {
    return ruleStore;
  }

  /**
   * Get the format string for this parser.
   * 
   * @return the format string.
   */
  public String getFormatString()
  {
    return "Option* Destination? Universesx?";
  }
}

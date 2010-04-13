
package org.jmlspecs.openjmlunit.clops;

import ie.ucd.clops.runtime.rules.RuleStore;

/**
 * The rule store is used to handle the constraints and the validity checks
 * associated with the options.
 * 
 * @author The CLOPS team (kind@ucd.ie)
 */
public class CmdOptionsRuleStore extends RuleStore
{

  public CmdOptionsRuleStore()
  {
  }

  protected final boolean shouldApplyFlyRulesTransitively()
  {
    return false;
  }
}

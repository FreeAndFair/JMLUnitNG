package org.jmlspecs.jmlunitng.clops;

import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.Action;
import ie.ucd.clops.runtime.rules.Expression;
import ie.ucd.clops.runtime.rules.OverrideRule;
import ie.ucd.clops.runtime.rules.RuleStore;

/**
 * The rule store is used to handle the constraints and the validity
 * checks associated with the options.
 * @author The CLOPS team (kind@ucd.ie)
 */
public class JMLUnitNGRuleStore extends RuleStore {
  
  public JMLUnitNGRuleStore() {
    Expression<Boolean> rule1Condition = new Rule1Condition();
    OverrideRule rule1 = new OverrideRule(rule1Condition);
    addOverrideRule(rule1);
    rule1.addAction(new Action<Boolean>("Public", new Rule1Expression1()));

    Expression<Boolean> rule2Condition = new Rule2Condition();
    OverrideRule rule2 = new OverrideRule(rule2Condition);
    addOverrideRule(rule2);
    rule2.addAction(new Action<Boolean>("Protected", new Rule2Expression2()));

    Expression<Boolean> rule3Condition = new Rule3Condition();
    OverrideRule rule3 = new OverrideRule(rule3Condition);
    addOverrideRule(rule3);
    rule3.addAction(new Action<Boolean>("Package", new Rule3Expression3()));

  }

  public static class Rule1Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Public")).hasValue();
    }
  }
    
  public static class Rule1Expression1 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return true;
    }
  }

  public static class Rule2Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Protected")).hasValue();
    }
  }
    
  public static class Rule2Expression2 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }

  public static class Rule3Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Package")).hasValue();
    }
  }
    
  public static class Rule3Expression3 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }


  protected final boolean shouldApplyFlyRulesTransitively() {
    return false;
  }
}

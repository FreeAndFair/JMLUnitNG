package org.jmlspecs.jmlunitng.clops;

import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.Action;
import ie.ucd.clops.runtime.rules.Expression;
import ie.ucd.clops.runtime.rules.FlyRule;
import ie.ucd.clops.runtime.rules.OverrideRule;
import ie.ucd.clops.runtime.rules.RuleStore;
import ie.ucd.clops.runtime.rules.ValidityRule;


import java.util.Arrays;
import java.util.List;

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

    Expression<Boolean> rule4Condition = new Rule4Condition();
    ValidityRule rule4 = new ValidityRule(rule4Condition);
    rule4.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule4Expression()));
    addValidityRule(rule4);
    Expression<Boolean> rule5Condition = new Rule5Condition();
    ValidityRule rule5 = new ValidityRule(rule5Condition);
    rule5.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule5Expression()));
    addValidityRule(rule5);
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

  public static class Rule4Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Package")).hasValue() && ((ie.ucd.clops.runtime.options.StringOption)optionStore.getOptionByIdentifier("TestPackage")).hasValue();
    }
  }
    
  public static class Rule4Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("You cannot specify a test package when testing package-level methods.");
    }
  }
  
  public static class Rule5Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Protected")).hasValue() && ((ie.ucd.clops.runtime.options.StringOption)optionStore.getOptionByIdentifier("TestPackage")).hasValue();
    }
  }
    
  public static class Rule5Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("You cannot specify a test package when testing protected methods.");
    }
  }
  

  protected final boolean shouldApplyFlyRulesTransitively() {
    return false;
  }
}

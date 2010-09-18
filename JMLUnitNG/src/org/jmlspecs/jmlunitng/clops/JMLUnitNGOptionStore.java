/*
 * JMLUnitNG 
 * Copyright (C) 2010
 */

package org.jmlspecs.jmlunitng.clops;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import java.util.List;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.StringOption;
import ie.ucd.clops.runtime.options.FileListOption;

public class JMLUnitNGOptionStore extends OptionStore implements JMLUnitNGOptionsInterface {

  private final StringOption ogDestination;
  private final StringOption ogRACVersion;
  private final FileListOption ogFiles;
  private final BooleanOption ogDashDash;
  private final FileListOption ogDashFiles;
  private final BooleanOption ogReflection;
  private final BooleanOption ogHelp;
  private final BooleanOption ogDeprecation;
  private final BooleanOption ogVerbose;
  private final BooleanOption ogInherited;
  private final BooleanOption ogPublic;
  private final BooleanOption ogProtected;
  private final BooleanOption ogPackage;
  private final BooleanOption ogClean;
  private final BooleanOption ogPrune;
  private final FileListOption ogClasspath;
  private final FileListOption ogSpecspath;
  private final BooleanOption ogDryRun;
  private final BooleanOption ogNoGen;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public JMLUnitNGOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogDestination = new StringOption("Destination", "(?:-d)|(?:--dest)");
    addOption(ogDestination);
    ogDestination.setProperty("aliases", "-d,--dest");
    ogRACVersion = new StringOption("RACVersion", "(?:--rac-version)");
    addOption(ogRACVersion);
    ogRACVersion.setProperty("aliases", "--rac-version");
    ogFiles = new FileListOption("Files", "");
    addOption(ogFiles);
    ogFiles.setProperty("allowmultiple", "false");
    ogFiles.setProperty("between", "");
    ogFiles.setProperty("mustexist", "true");
    ogFiles.setProperty("canbedir", "true");
    ogFiles.setProperty("allowdash", "false");
    ogDashDash = new BooleanOption("DashDash", "(?:--)");
    addOption(ogDashDash);
    ogDashDash.setProperty("aliases", "--");
    ogDashFiles = new FileListOption("DashFiles", "");
    addOption(ogDashFiles);
    ogDashFiles.setProperty("allowmultiple", "false");
    ogDashFiles.setProperty("between", "");
    ogDashFiles.setProperty("mustexist", "true");
    ogDashFiles.setProperty("canbedir", "true");
    ogDashFiles.setProperty("allowdash", "true");
    ogReflection = new BooleanOption("Reflection", "(?:--reflection)");
    addOption(ogReflection);
    ogReflection.setProperty("aliases", "--reflection");
    ogHelp = new BooleanOption("Help", "(?:-h)|(?:--help)");
    addOption(ogHelp);
    ogHelp.setProperty("aliases", "-h,--help");
    ogDeprecation = new BooleanOption("Deprecation", "(?:--deprecation)");
    addOption(ogDeprecation);
    ogDeprecation.setProperty("aliases", "--deprecation");
    ogVerbose = new BooleanOption("Verbose", "(?:-v)|(?:--verbose)");
    addOption(ogVerbose);
    ogVerbose.setProperty("aliases", "-v,--verbose");
    ogInherited = new BooleanOption("Inherited", "(?:--inherited)");
    addOption(ogInherited);
    ogInherited.setProperty("aliases", "--inherited");
    ogPublic = new BooleanOption("Public", "(?:--public)");
    addOption(ogPublic);
    ogPublic.setProperty("aliases", "--public");
    ogProtected = new BooleanOption("Protected", "(?:--protected)");
    addOption(ogProtected);
    ogProtected.setProperty("aliases", "--protected");
    ogPackage = new BooleanOption("Package", "(?:--package)");
    addOption(ogPackage);
    ogPackage.setProperty("aliases", "--package");
    ogClean = new BooleanOption("Clean", "(?:--clean)");
    addOption(ogClean);
    ogClean.setProperty("aliases", "--clean");
    ogPrune = new BooleanOption("Prune", "(?:--prune)");
    addOption(ogPrune);
    ogPrune.setProperty("aliases", "--prune");
    ogClasspath = new FileListOption("Classpath", "(?:-cp)|(?:--classpath)");
    addOption(ogClasspath);
    ogClasspath.setProperty("allowmultiple", "true");
    ogClasspath.setProperty("splitter", ":");
    ogClasspath.setProperty("mustexist", "true");
    ogClasspath.setProperty("mustbedir", "true");
    ogClasspath.setProperty("aliases", "-cp,--classpath");
    ogSpecspath = new FileListOption("Specspath", "(?:-sp)|(?:--specspath)");
    addOption(ogSpecspath);
    ogSpecspath.setProperty("allowmultiple", "true");
    ogSpecspath.setProperty("splitter", ":");
    ogSpecspath.setProperty("mustexist", "true");
    ogSpecspath.setProperty("mustbedir", "true");
    ogSpecspath.setProperty("aliases", "-sp,--specspath");
    ogDryRun = new BooleanOption("DryRun", "(?:--dry-run)");
    addOption(ogDryRun);
    ogDryRun.setProperty("aliases", "--dry-run");
    ogNoGen = new BooleanOption("NoGen", "(?:--no-gen)");
    addOption(ogNoGen);
    ogNoGen.setProperty("aliases", "--no-gen");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup ogOption = new OptionGroup("Option");
    addOptionGroup(ogOption);
    final OptionGroup ogAllOptions = new OptionGroup("AllOptions");
    addOptionGroup(ogAllOptions);
    
    //Setup groupings
    ogOption.addOptionOrGroup(ogVerbose);
    ogOption.addOptionOrGroup(ogPrune);
    ogOption.addOptionOrGroup(ogClasspath);
    ogOption.addOptionOrGroup(ogDeprecation);
    ogOption.addOptionOrGroup(ogNoGen);
    ogOption.addOptionOrGroup(ogClean);
    ogOption.addOptionOrGroup(ogProtected);
    ogOption.addOptionOrGroup(ogHelp);
    ogOption.addOptionOrGroup(ogSpecspath);
    ogOption.addOptionOrGroup(ogReflection);
    ogOption.addOptionOrGroup(ogDryRun);
    ogOption.addOptionOrGroup(ogPackage);
    ogOption.addOptionOrGroup(ogDestination);
    ogOption.addOptionOrGroup(ogRACVersion);
    ogOption.addOptionOrGroup(ogPublic);
    ogOption.addOptionOrGroup(ogInherited);
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogDestination);
    ogAllOptions.addOptionOrGroup(ogRACVersion);
    ogAllOptions.addOptionOrGroup(ogFiles);
    ogAllOptions.addOptionOrGroup(ogDashDash);
    ogAllOptions.addOptionOrGroup(ogDashFiles);
    ogAllOptions.addOptionOrGroup(ogReflection);
    ogAllOptions.addOptionOrGroup(ogHelp);
    ogAllOptions.addOptionOrGroup(ogDeprecation);
    ogAllOptions.addOptionOrGroup(ogVerbose);
    ogAllOptions.addOptionOrGroup(ogInherited);
    ogAllOptions.addOptionOrGroup(ogPublic);
    ogAllOptions.addOptionOrGroup(ogProtected);
    ogAllOptions.addOptionOrGroup(ogPackage);
    ogAllOptions.addOptionOrGroup(ogClean);
    ogAllOptions.addOptionOrGroup(ogPrune);
    ogAllOptions.addOptionOrGroup(ogClasspath);
    ogAllOptions.addOptionOrGroup(ogSpecspath);
    ogAllOptions.addOptionOrGroup(ogDryRun);
    ogAllOptions.addOptionOrGroup(ogNoGen);
  }
  
// Option Destination.
// Aliases: [-d, --dest]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDestinationSet() {
    return ogDestination.hasValue();
  }
  
  /** {@inheritDoc} */
  public String getDestination() {
    return ogDestination.getValue();
  }

  /** {@inheritDoc} */
  public String getRawDestination() {
    return ogDestination.getRawValue();
  }
  
  public StringOption getDestinationOption() {
    return ogDestination;
  }
  
// Option RACVersion.
// Aliases: [--rac-version]
  
  /**
   * {@inheritDoc}
   */
  public boolean isRACVersionSet() {
    return ogRACVersion.hasValue();
  }
  
  /** {@inheritDoc} */
  public String getRACVersion() {
    return ogRACVersion.getValue();
  }

  /** {@inheritDoc} */
  public String getRawRACVersion() {
    return ogRACVersion.getRawValue();
  }
  
  public StringOption getRACVersionOption() {
    return ogRACVersion;
  }
  
// Option Files.
// Aliases: []
  
  /**
   * {@inheritDoc}
   */
  public boolean isFilesSet() {
    return ogFiles.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getFiles() {
    return ogFiles.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawFiles() {
    return ogFiles.getRawValue();
  }
  
  public FileListOption getFilesOption() {
    return ogFiles;
  }
  
// Option DashDash.
// Aliases: [--]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDashDashSet() {
    return ogDashDash.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getDashDash() {
    return ogDashDash.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawDashDash() {
    return ogDashDash.getRawValue();
  }
  
  public BooleanOption getDashDashOption() {
    return ogDashDash;
  }
  
// Option DashFiles.
// Aliases: []
  
  /**
   * {@inheritDoc}
   */
  public boolean isDashFilesSet() {
    return ogDashFiles.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getDashFiles() {
    return ogDashFiles.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawDashFiles() {
    return ogDashFiles.getRawValue();
  }
  
  public FileListOption getDashFilesOption() {
    return ogDashFiles;
  }
  
// Option Reflection.
// Aliases: [--reflection]
  
  /**
   * {@inheritDoc}
   */
  public boolean isReflectionSet() {
    return ogReflection.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getReflection() {
    return ogReflection.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawReflection() {
    return ogReflection.getRawValue();
  }
  
  public BooleanOption getReflectionOption() {
    return ogReflection;
  }
  
// Option Help.
// Aliases: [-h, --help]
  
  /**
   * {@inheritDoc}
   */
  public boolean isHelpSet() {
    return ogHelp.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getHelp() {
    return ogHelp.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawHelp() {
    return ogHelp.getRawValue();
  }
  
  public BooleanOption getHelpOption() {
    return ogHelp;
  }
  
// Option Deprecation.
// Aliases: [--deprecation]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDeprecationSet() {
    return ogDeprecation.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getDeprecation() {
    return ogDeprecation.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawDeprecation() {
    return ogDeprecation.getRawValue();
  }
  
  public BooleanOption getDeprecationOption() {
    return ogDeprecation;
  }
  
// Option Verbose.
// Aliases: [-v, --verbose]
  
  /**
   * {@inheritDoc}
   */
  public boolean isVerboseSet() {
    return ogVerbose.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getVerbose() {
    return ogVerbose.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawVerbose() {
    return ogVerbose.getRawValue();
  }
  
  public BooleanOption getVerboseOption() {
    return ogVerbose;
  }
  
// Option Inherited.
// Aliases: [--inherited]
  
  /**
   * {@inheritDoc}
   */
  public boolean isInheritedSet() {
    return ogInherited.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getInherited() {
    return ogInherited.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawInherited() {
    return ogInherited.getRawValue();
  }
  
  public BooleanOption getInheritedOption() {
    return ogInherited;
  }
  
// Option Public.
// Aliases: [--public]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPublicSet() {
    return ogPublic.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPublic() {
    return ogPublic.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPublic() {
    return ogPublic.getRawValue();
  }
  
  public BooleanOption getPublicOption() {
    return ogPublic;
  }
  
// Option Protected.
// Aliases: [--protected]
  
  /**
   * {@inheritDoc}
   */
  public boolean isProtectedSet() {
    return ogProtected.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getProtected() {
    return ogProtected.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawProtected() {
    return ogProtected.getRawValue();
  }
  
  public BooleanOption getProtectedOption() {
    return ogProtected;
  }
  
// Option Package.
// Aliases: [--package]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPackageSet() {
    return ogPackage.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPackage() {
    return ogPackage.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPackage() {
    return ogPackage.getRawValue();
  }
  
  public BooleanOption getPackageOption() {
    return ogPackage;
  }
  
// Option Clean.
// Aliases: [--clean]
  
  /**
   * {@inheritDoc}
   */
  public boolean isCleanSet() {
    return ogClean.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getClean() {
    return ogClean.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawClean() {
    return ogClean.getRawValue();
  }
  
  public BooleanOption getCleanOption() {
    return ogClean;
  }
  
// Option Prune.
// Aliases: [--prune]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPruneSet() {
    return ogPrune.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPrune() {
    return ogPrune.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPrune() {
    return ogPrune.getRawValue();
  }
  
  public BooleanOption getPruneOption() {
    return ogPrune;
  }
  
// Option Classpath.
// Aliases: [-cp, --classpath]
  
  /**
   * {@inheritDoc}
   */
  public boolean isClasspathSet() {
    return ogClasspath.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getClasspath() {
    return ogClasspath.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawClasspath() {
    return ogClasspath.getRawValue();
  }
  
  public FileListOption getClasspathOption() {
    return ogClasspath;
  }
  
// Option Specspath.
// Aliases: [-sp, --specspath]
  
  /**
   * {@inheritDoc}
   */
  public boolean isSpecspathSet() {
    return ogSpecspath.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getSpecspath() {
    return ogSpecspath.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawSpecspath() {
    return ogSpecspath.getRawValue();
  }
  
  public FileListOption getSpecspathOption() {
    return ogSpecspath;
  }
  
// Option DryRun.
// Aliases: [--dry-run]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDryRunSet() {
    return ogDryRun.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getDryRun() {
    return ogDryRun.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawDryRun() {
    return ogDryRun.getRawValue();
  }
  
  public BooleanOption getDryRunOption() {
    return ogDryRun;
  }
  
// Option NoGen.
// Aliases: [--no-gen]
  
  /**
   * {@inheritDoc}
   */
  public boolean isNoGenSet() {
    return ogNoGen.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getNoGen() {
    return ogNoGen.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawNoGen() {
    return ogNoGen.getRawValue();
  }
  
  public BooleanOption getNoGenOption() {
    return ogNoGen;
  }
  
}

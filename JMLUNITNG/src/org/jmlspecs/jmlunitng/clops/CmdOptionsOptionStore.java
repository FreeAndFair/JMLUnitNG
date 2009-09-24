package org.jmlspecs.jmlunitng.clops;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import java.util.List;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.StringOption;
import ie.ucd.clops.runtime.options.FileListOption;

public class CmdOptionsOptionStore extends OptionStore implements CmdOptionsOptionsInterface {

  private final StringOption ogDestination;
  private final FileListOption ogList;
  private final BooleanOption ogHelp;
  private final FileListOption ogPackage;
  private final BooleanOption ogUniverses;
  private final BooleanOption ogDeprication;
  private final BooleanOption ogSafeMath;
  private final BooleanOption ogVerbose;
  private final StringOption ogUniversesx;
  private final BooleanOption ogInherited;
  private final BooleanOption ogPublic;
  private final BooleanOption ogProtected;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CmdOptionsOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogDestination = new StringOption("Destination", "(?:-d)|(?:--dest)");
    addOption(ogDestination);
    ogDestination.setProperty("aliases", "-d,--dest");
    ogList = new FileListOption("List", "(?:-f)|(?:--files)");
    addOption(ogList);
    ogList.setProperty("allowmultiple", "true");
    ogList.setProperty("splitter", ",");
    ogList.setProperty("mustexist", "true");
    ogList.setProperty("canbedir", "false");
    ogList.setProperty("allowdash", "true");
    ogList.setProperty("aliases", "-f,--files");
    ogHelp = new BooleanOption("Help", "(?:-h)|(?:--help)");
    addOption(ogHelp);
    ogHelp.setProperty("aliases", "-h,--help");
    ogPackage = new FileListOption("Package", "(?:-p)|(?:--package)");
    addOption(ogPackage);
    ogPackage.setProperty("allowmultiple", "true");
    ogPackage.setProperty("splitter", ",");
    ogPackage.setProperty("mustbedir", "true");
    ogPackage.setProperty("allowdash", "true");
    ogPackage.setProperty("aliases", "-p,--package");
    ogUniverses = new BooleanOption("Universes", "(?:-u)|(?:--universes)");
    addOption(ogUniverses);
    ogUniverses.setProperty("aliases", "-u,--universes");
    ogDeprication = new BooleanOption("Deprication", "(?:-dep)|(?:--deprication)");
    addOption(ogDeprication);
    ogDeprication.setProperty("aliases", "-dep,--deprication");
    ogSafeMath = new BooleanOption("SafeMath", "(?:-s)|(?:--safemath)");
    addOption(ogSafeMath);
    ogSafeMath.setProperty("aliases", "-s,--safemath");
    ogVerbose = new BooleanOption("Verbose", "(?:-v)|(?:--verbose)");
    addOption(ogVerbose);
    ogVerbose.setProperty("aliases", "-v,--verbose");
    ogUniversesx = new StringOption("Universesx", "(?:-E)");
    addOption(ogUniversesx);
    ogUniversesx.setProperty("aliases", "-E");
    ogInherited = new BooleanOption("Inherited", "(?:-inherited)");
    addOption(ogInherited);
    ogInherited.setProperty("aliases", "-inherited");
    ogPublic = new BooleanOption("Public", "(?:-public)");
    addOption(ogPublic);
    ogPublic.setProperty("aliases", "-public");
    ogProtected = new BooleanOption("Protected", "(?:-protected)");
    addOption(ogProtected);
    ogProtected.setProperty("aliases", "-protected");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup ogOption = new OptionGroup("Option");
    addOptionGroup(ogOption);
    final OptionGroup ogAllOptions = new OptionGroup("AllOptions");
    addOptionGroup(ogAllOptions);
    
    //Setup groupings
    ogOption.addOptionOrGroup(ogVerbose);
    ogOption.addOptionOrGroup(ogHelp);
    ogOption.addOptionOrGroup(ogSafeMath);
    ogOption.addOptionOrGroup(ogDeprication);
    ogOption.addOptionOrGroup(ogUniverses);
    ogOption.addOptionOrGroup(ogPackage);
    ogOption.addOptionOrGroup(ogProtected);
    ogOption.addOptionOrGroup(ogList);
    ogOption.addOptionOrGroup(ogUniversesx);
    ogOption.addOptionOrGroup(ogDestination);
    ogOption.addOptionOrGroup(ogPublic);
    ogOption.addOptionOrGroup(ogInherited);
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogDestination);
    ogAllOptions.addOptionOrGroup(ogList);
    ogAllOptions.addOptionOrGroup(ogHelp);
    ogAllOptions.addOptionOrGroup(ogPackage);
    ogAllOptions.addOptionOrGroup(ogUniverses);
    ogAllOptions.addOptionOrGroup(ogDeprication);
    ogAllOptions.addOptionOrGroup(ogSafeMath);
    ogAllOptions.addOptionOrGroup(ogVerbose);
    ogAllOptions.addOptionOrGroup(ogUniversesx);
    ogAllOptions.addOptionOrGroup(ogInherited);
    ogAllOptions.addOptionOrGroup(ogPublic);
    ogAllOptions.addOptionOrGroup(ogProtected);
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
  
// Option List.
// Aliases: [-f, --files]
  
  /**
   * {@inheritDoc}
   */
  public boolean isListSet() {
    return ogList.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getList() {
    return ogList.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawList() {
    return ogList.getRawValue();
  }
  
  public FileListOption getListOption() {
    return ogList;
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
  
// Option Package.
// Aliases: [-p, --package]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPackageSet() {
    return ogPackage.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getPackage() {
    return ogPackage.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawPackage() {
    return ogPackage.getRawValue();
  }
  
  public FileListOption getPackageOption() {
    return ogPackage;
  }
  
// Option Universes.
// Aliases: [-u, --universes]
  
  /**
   * {@inheritDoc}
   */
  public boolean isUniversesSet() {
    return ogUniverses.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getUniverses() {
    return ogUniverses.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawUniverses() {
    return ogUniverses.getRawValue();
  }
  
  public BooleanOption getUniversesOption() {
    return ogUniverses;
  }
  
// Option Deprication.
// Aliases: [-dep, --deprication]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDepricationSet() {
    return ogDeprication.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getDeprication() {
    return ogDeprication.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawDeprication() {
    return ogDeprication.getRawValue();
  }
  
  public BooleanOption getDepricationOption() {
    return ogDeprication;
  }
  
// Option SafeMath.
// Aliases: [-s, --safemath]
  
  /**
   * {@inheritDoc}
   */
  public boolean isSafeMathSet() {
    return ogSafeMath.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getSafeMath() {
    return ogSafeMath.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawSafeMath() {
    return ogSafeMath.getRawValue();
  }
  
  public BooleanOption getSafeMathOption() {
    return ogSafeMath;
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
  
// Option Universesx.
// Aliases: [-E]
  
  /**
   * {@inheritDoc}
   */
  public boolean isUniversesxSet() {
    return ogUniversesx.hasValue();
  }
  
  /** {@inheritDoc} */
  public String getUniversesx() {
    return ogUniversesx.getValue();
  }

  /** {@inheritDoc} */
  public String getRawUniversesx() {
    return ogUniversesx.getRawValue();
  }
  
  public StringOption getUniversesxOption() {
    return ogUniversesx;
  }
  
// Option Inherited.
// Aliases: [-inherited]
  
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
// Aliases: [-public]
  
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
// Aliases: [-protected]
  
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
  
}

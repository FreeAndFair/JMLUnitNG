/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjmlunit.generator.ClassInfo;
import org.jmlspecs.openjmlunit.generator.InfoFactory;
import org.jmlspecs.openjmlunit.generator.MethodInfo;

/**
 * "The main executable."
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public final class Main {
  /**
   * Private constructor to prevent initilization.
   */
  private Main() {
  }

  /**
   * Tool entry point. Test bed for now.
   * 
   * @param the_args Arguments from the command line.
   */
  public static void main(final String[] the_args) {
    try {
      //assume current directory is project root
      final String workspace = System.getProperty("user.dir");
      final String[] arg =
          new String[] {"-noPurityCheck", "-noInternalSpecs", "-cp", workspace + "/src"};
      final API api = new API(arg);
      //replace with file to test
      final String testSrc = workspace + "/src/org/jmlspecs/" + 
              "openjmlunit/generator/InfoFactory.java";
      final List<JmlCompilationUnit> units = api.parseFiles(new File(testSrc));
      final int numOfErrors = api.enterAndCheck(units);
      if (numOfErrors > 0) {
        System.err.println("Error: " + numOfErrors);
      } else {
        System.out.println("Units: " + units.size());
        for (JmlCompilationUnit unit : units) {
          final ClassInfo info = InfoFactory.getClassInfo(unit);
          System.out.println("Name: " + info.getName());
          System.out.println("Parent Name: " + info.getSuperclassInfo().getName());
          System.out.println("Prot Level: " + info.getProtectionLevel().toString());
          System.out.println("Testable methods:");
          for (MethodInfo m : info.getTestableMethods()) {
            System.out.println("Method Name: " + m.getName() + " Ret Type: " +
                               m.getReturnType() + " Prot Level: " +
                               m.getProtectionLevel().toString());
          }
        }
      }
    } catch (final IOException e) {
      e.printStackTrace();
    }
  }

}


package org.jmlspecs.jmlunitng;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.jmlspecs.jmlunitng.clops.CmdOptionsOptionsInterface;
import org.jmlspecs.jmlunitng.clops.CmdOptionsParser;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

/**
 * Test.
 * 
 * @author rinkeshn
 * 
 */
public class Test
{

  /**
   * @param args
   * @throws InvalidOptionPropertyValueException
   * @throws InvalidOptionValueException
   * @throws AutomatonException
   * @throws IOException
   */
  public static void main(String[] args) throws InvalidOptionPropertyValueException,
      AutomatonException, InvalidOptionValueException, IOException
  {
    CmdOptionsParser parser = new CmdOptionsParser();

    parser.parse(args);
    CmdOptionsOptionsInterface inf = parser.getOptionStore();

    if (inf.isDestinationSet())
    {
      System.out.println("destination " + inf.getDestination());
    }
    if (inf.isListSet())
    {
      List<File> s = inf.getList();
      for (int i = 0; i < s.size(); i++)
      {
        System.out.println(s.get(i).getCanonicalPath());
      }
    }
    if (inf.isPackageSet())
    {
      List<File> dir = inf.getPackage();
      for (int i = 0; i < dir.size(); i++)
      {
        File[] files = dir.get(i).listFiles();
        for (int j = 0; j < files.length; j++)
        {
          System.out.println(files[j].getPath());
        }
      }
    }
  }

}

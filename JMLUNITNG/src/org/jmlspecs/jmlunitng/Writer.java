
package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

/**
 * Constructs a Writer Object.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 * */
public class Writer
{

  /** PrintWriter object to write string to the file. */
  private PrintWriter p;
  /** String to mention the file name for the class. */
  private String file;

  /**
   * Constructs a Writer object for java code.
   * 
   * @param fileName
   *@throws FileNotFoundException;
   */
  public Writer(final String the_fileName) throws FileNotFoundException
  {
    file = the_fileName;
    p = new PrintWriter(file);
  }

  /**
   * Prints the string to the file.
   * 
   * @param s String which will be printed in the file.
   */
  protected final void print(final String the_line)
  {
    p.print(the_line + "\n");
    p.flush();
  }

  /**
   * Prints without a newline character.
   */
  protected final void printOnLine(final String the_line)
  {
    p.print(the_line);
  }

  /**
   * Print a newline.
   */
  protected final void newLine(final int the_numberOfNewLines)
  {
    for (int i = 0; i < the_numberOfNewLines; i++)
    {
      p.print("\n");
    }
    p.flush();
  }

  /**
   * Indent a space.
   */
  protected final void indent(final int the_numberOfIndent)
  {
    for (int i = 0; i < the_numberOfIndent; i++)
    {
      p.print(" ");
    }
    p.flush();
  }

}

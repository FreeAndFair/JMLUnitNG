
package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

/**
 * Constructs a Writer Object.
 * 
 * @author Rinkesh Nagmoti
 * @version 1.0
 * */
public class Writer implements Constants
{

  /** PrintWriter object to write string to the file. */
  private final transient PrintWriter my_print_writer;


  /**
   * Constructs a Writer object for java code.
   * 
   * @param the_file_name String name of the file.
   *@throws FileNotFoundException Exception if unable to find specified file. 
   */
  public Writer(final String the_file_name) throws FileNotFoundException
  {
    final String my_file = the_file_name;
    my_print_writer = new PrintWriter(my_file);
  }

  /**
   * Prints the string to the file.
   * 
   * @param the_line String which will be printed in the file.
   */
  protected final void print(final String the_line)
  {
    my_print_writer.print(the_line + "\n");
    my_print_writer.flush();
  }

  /**
   * Prints without a newline character.
   * @param the_line The line to be printed.
   */
  protected final void printOnLine(final String the_line)
  {
    my_print_writer.print(the_line);
  }

  /**
   * Print a newline.
   * @param the_new_lines The number of new lines to be inserted.
   */
  protected final void newLine(final int the_new_lines)
  {
    for (int i = 0; i < the_new_lines; i++)
    {
      my_print_writer.print("\n");
    }
    my_print_writer.flush();
  }

  /**
   * Indent a space.
   * @param the_indent The number of spaces for indentation.
   */
  protected final void indent(final int the_indent)
  {
    for (int i = 0; i < the_indent; i++)
    {
      my_print_writer.print(" ");
    }
    my_print_writer.flush();
  }

}

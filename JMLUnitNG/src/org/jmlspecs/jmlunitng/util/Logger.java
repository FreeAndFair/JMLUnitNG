/*
 * JMLUnitNG 
 * Copyright (C) 2010-11
 */

package org.jmlspecs.jmlunitng.util;

/**
 * A class that handles rudimentary logging output.
 * 
 * @author Daniel M. Zimmerman
 * @version September 2010
 */
public class Logger {
  /**
   * true if we will actually generate output, false otherwise.
   */
  private final boolean my_output;
  
  /**
   * Constructs a logger that will either print output to standard out
   * or stay quiet.
   * 
   * @param the_output true to print output, false to stay quiet.
   */
  public Logger(final boolean the_output) {
    my_output = the_output;
  }
  
  /**
   * Log a blank line!
   */
  public void println() {
    if (my_output) {
      System.out.println();
    }
  }
  
  /**
   * Log the_line!
   * 
   * @param the_line The line to log.
   */
  public void println(final String the_line) {
    if (my_output) {
      System.out.println(the_line);
    }
  }
  
  /**
   * Log the_text without a line break at the end!
   * 
   * @param the_text The text to log.
   */
  public void print(final String the_text) {
    if (my_output) {
      System.out.print(the_text);
    }
  }
}

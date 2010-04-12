/*
 * OpenJMLUnit
 * 
 * @author "Jonathan Hogins (jon.hogins@gmail.com)"
 * 
 * @module "OpenJML"
 * 
 * @creation_date "April 2010"
 * 
 * @last_updated_date "April 2010"
 * 
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.generator;

import java.io.IOException;
import java.io.Writer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Formats and outputs source code to a StringOutputStream.
 * 
 * @author Jonathan Hogins
 * @version April 2010
 */
public class SourceWriter {
  /**
   * The system newline string used for writeLine.
   */
  public static final String NEWLINE = System.getProperty("line.separator");
  /**
   * The java block start character.
   */
  private static final String BLOCK_START = "{";
  /**
   * The java block end character.
   */
  private static final String BLOCK_END = "}";
  /**
   * The prefix to use for Javadoc comment lines.
   */
  private static final String JAVADOC_PREFIX = " * ";
  /**
   * The Javadoc block start character.
   */
  private static final String JAVADOC_BLOCK_START = "\\*";
  /**
   * The Javadoc block end character.
   */
  private static final String JAVADOC_BLOCK_END = " */";
  /**
   * The pattern for finding newline characters.
   */
  private static final Pattern NEWLINE_PATTERN = Pattern.compile("([^.])");
  /**
   * Default IndentCharacter to use for code indentation.
   */
  private static char DEFAULT_INDENT_CHAR = ' ';
  /**
   * Default indent size.
   */
  private static int DEFAULT_INDENT_SIZE = 1;
  /**
   * The current indent level.
   */
  // @ invariant my_indent_level >= 0;
  private int my_indent_level;
  /**
   * The number of characters to use for indents.
   */
  // @ invariant my_indent_size >= 0;
  private int my_indent_size;
  /**
   * Char to use for indentation.
   */
  private char my_indent_char;
  /**
   * What level java block am I in? -1 is a Javadoc comment.
   */
  // @ invariant my_block_level >= -1;
  private int my_block_level;
  /**
   * Have any characters been written to the current line?
   */
  private boolean my_chars_on_cur_line;
  /**
   * The writer containing the stream to write to.
   */
  private Writer my_writer;

  /**
   * Creates a new SourceWriter whose output is sent to the_writer.
   * 
   * @param the_writer The writer to use for source output.
   */
  public SourceWriter(final Writer the_writer) {
    this(the_writer, DEFAULT_INDENT_SIZE, DEFAULT_INDENT_CHAR);
  }

  /**
   * Creates a new SourceWriter whose output is sent to the_writer. Indents will
   * be composed of the_indent_char repeated the_indent_size times.
   * 
   * @param the_writer The writer to use for source output.
   * @param the_indent_size The number of characters to be written for each
   *          indent level.
   * @param the_indent_char The char to use for indentation.
   */
  public SourceWriter(final Writer the_writer, final int the_indent_size,
                      final char the_indent_char) {
    my_writer = the_writer;
    my_indent_level = 0;
    my_indent_size = the_indent_size;
    my_indent_char = the_indent_char;
    my_block_level = 0;
    my_chars_on_cur_line = false;
  }

  /**
   * What is the current indent level? Default is 0.
   * 
   * @return The current indent level.
   */
  // @ensures \result == my_indent_level;
  public int getIndentLevel() {
    return my_indent_level;
  }

  /**
   * Prints the given string followed by a newline character to the output
   * stream. The line prefix is prepended to the_string if this is the first
   * write to the current line.
   * 
   * @param the_string The string to write.
   * @throws IOException an IOException occurred when attempting to append to
   *           the writer.
   */
  // @ ensures !my_chars_on_cur_line;
  public void writeLine(final String the_string) throws IOException {
    my_writer.append(formatString(the_string) + NEWLINE);
    my_chars_on_cur_line = false;
  }

  /**
   * Prints the given string to the output stream. If this is the first call to
   * either write since construction or the last call to writeLine, the string
   * is formatted first for indentation and/or comment characters.
   * 
   * @param the_string The string to format and output.
   * @throws IOException an IOException occurred when attempting to append to
   *           the writer.
   */
  // @ ensures my_chars_on_cur_line;
  public void write(final String the_string) throws IOException {
    my_writer.append(formatString(the_string));
    my_chars_on_cur_line = true;
  }

  /**
   * Changes the indent level to the_new_level.
   * 
   * @param the_new_level The new indent level.
   */
  /*@ requires the_new_level >= 0;
    @ ensures my_indent_level == the_new_level;
   */
  public void setIndentLevel(final int the_new_level) {
    my_indent_level = the_new_level;
  }

  // "Increase the indent level by 1!",
  /**
   * Increments the indent level by 1.
   */
  // @ ensures \old (my_indent_level) == my_indent_level - 1;
  public void incrementIndentLevel() {
    my_indent_level++;
  }

  /**
   * Decrements the indent level by 1. The indent level must be at least 1.
   */
  /* @ requires my_indent_level > 0;
     @ ensures \old (my_indent_level) == my_indent_level + 1; 
   */
  public void decrementIndentLevel() {
    my_indent_level--;
  }
  
  /**
   * Is the writer writing a Javadoc block?
   * 
   * @return True if writing a javadoc block. False otherwise.
   */
  //@ ensures \result == (my_block_level == -1);
  public boolean isWritingJavadoc() {
    return my_block_level == -1;
  }
  
  /**
   * Starts a java block. This increases the indent level by 1. Must not be
   * writing a Javadoc block.
   * 
   * @throws IOException an IOException occurred when attempting to append to
   *           the writer.
   */
  /*@ requires my_block_level == -1;
    @ ensures (\old (my_indent_level) == my_indent_level - 1) &&
    @         (\old (my_block_level) == my_block_level - 1);
   */
  public void startJavaBlock() throws IOException {
    incrementIndentLevel();
    writeLine(BLOCK_START);
    my_block_level++;
  }

  /**
   * Ends a java block. This decreases the indent level by 1.
   * 
   * @throws IOException an IOException occurred when attempting to append to
   *           the writer.
   * @throws IllegalStateException Thrown when block level is 0;
   */
  /*@ requires my_block_level < 1;
    @ ensures (\old (my_indent_level) == my_indent_level + 1) &&
    @         (\old (my_block_level) == my_block_level + 1);
   */
  public void endJavaBlock() throws IOException {
    incrementIndentLevel();
    writeLine(BLOCK_END);
    my_block_level++;
  }

  // "Start a Javadoc block!",
  /**
   * Starts a new Javadoc block. Must not be writing a Javadoc or Java block.
   * 
   * @throws IOException an IOException occurred when attempting to append to
   *           the writer.
   */
    //@ requires my_block_level != 0;
  public void startJavadocBlock() throws IOException {
    my_block_level = -1;
    writeLine(JAVADOC_BLOCK_START);
  }

  /**
   * Ends the Javadoc block. Must be writing a Javadoc block.
   * 
   * @throws IOException an IOException occurred when attempting to append to
   *           the writer.
   */
  /*@ requires my_block_level < 1;
    @ ensures (\old (my_indent_level) == my_indent_level + 1) &&
    @         (\old (my_block_level) == my_block_level + 1);
   */
  public void endJavadocBlock() throws IOException {
    writeLine(JAVADOC_BLOCK_END);
    my_block_level++;
  }

  // "End the current Javadoc block!"
  /**
   * Returns the current line suffix based on indent level/java block.
   * 
   * @return The current line suffix.
   */
  public String getLinePrefix() {
    final StringBuilder sb = new StringBuilder();
    for (int i = 0; i < my_indent_level; i++) {
      for (int j = 0; j < my_indent_size; j++) {
        sb.append(my_indent_char);
      }
    }
    // Javadoc level
    if (my_block_level == -1) {
      sb.append(JAVADOC_PREFIX);
    }
    return sb.toString();
  }

  /**
   * Return a formatted version of the given string. A formatted string is
   * transformed as follows:
   * 
   * <ul>
   * <li>getLinePrefix() prepended if write() has not been called on this line
   * previously.</li>
   * <li>getLinePrefix() and a single indent character are inserted after each
   * newline character.</li>
   * </ul>
   * 
   * @param the_string The string to format.
   * @return The formatted string.
   */
  private String formatString(final String the_string) {
    final StringBuffer sb = new StringBuffer();
    if (!my_chars_on_cur_line) {
      sb.append(getLinePrefix());
    }
    final Matcher match = NEWLINE_PATTERN.matcher(the_string);
    match.appendReplacement(sb, "$1" + getLinePrefix() + my_indent_char);
    return sb.toString();
  }
}

package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

/** Constructs a Writer Object.*/
public class Writer {
	/** Constructs a Writer object for java code.
	 * @param fileName String != null;
	 * @throws FileNotFoundException;
	 */
	public Writer(String fileName) throws FileNotFoundException {
		file = "C:\\rinkesh.java";
		p = new PrintWriter(file);
	}

	/** Prints the string to the file.
	 *  @param s String which will be printed in the file.
	 */
	protected final void print(String s) {
		p.print(s);
		p.flush();
	}
	/**
	 * Print a newline.
	 */
	protected final void newLine() {
		p.print("\n");
	}
	/**
	 * Indent a tab.
	 */
	protected final void tab() {
		p.print("   ");
	}
	 // ---------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------

	/**PrintWriter object to write string to the file.*/
	private PrintWriter p;
	/**String to mention the file name for the class.*/
	private String file;
}

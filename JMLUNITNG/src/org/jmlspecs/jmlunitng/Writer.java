package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

public class Writer {
 
	/** Constructs a Writer object for java code */
	public Writer(String fileName) throws FileNotFoundException
	{
		file = "C:\\rinkesh.java";
		p = new PrintWriter(file);
	}
	
	/** Prints the string to the file 
	 *  @param s String which will be printed in the file
	 */
	public void print(String s){
		
		p.print(s);
		p.flush();
	}
	/**
	 * Print a newline.
	 */
	public void newLine(){
		p.print("\n");
	}
	 // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

	private PrintWriter p;
	private String file ;
	

}

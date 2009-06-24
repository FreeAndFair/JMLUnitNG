package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.util.Date;

/**
 * A class which generates the test oracle class for the class to be tested.
 * 
 * @author Rinkesh Nagmoti
 * @version 
 */
public class TestClassGenerator implements Constants{

    // ----------------------------------------------------------------------
    // CONSTRUCTOR
    // ----------------------------------------------------------------------
	public TestClassGenerator() throws FileNotFoundException
	{
		writer = new Writer();
	}
	public void perform()
	{
		//Generates the Test oracle class.
	}
	protected void generateTestClass()
	{
		// Generated the test oracle. Calls all other methods to generate oracle.
	}
	
	/** Prints the file header to the Test File */
	protected void printFileHeader() {
		  writer.print("This file is created by JMLUNITNG on"+ new Date()+".");
	 }
	
	protected void printImportStatements()
	 {
		//Prints import statements 
	 }
	protected void printClassJavadoc ()
	{
		// Prints class java docs
	}
	protected void printClassHeader()
	{
		//Prints the class header.
	}
	protected void initializeFixture()
	{
		//Initialize the parameters.
	}
	protected void printConstructor() {
		 //prints constructor.
	 }
	protected void printMain() {
		//Calls run method from TestRunner class.
	}
	protected void printSuite() {
		
	}
	private boolean preconditionPass(){
		return true;
		//returns false if the precondition violation exception occurs. Need to throw PreconditionViolationSkipException. 
	}
	/*
	 * There are many other private and protected methods which I will need to create. One class need to be created for storing 
	 * parameters used by these methods.
	 */
	
    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
	
	private Writer writer;
}

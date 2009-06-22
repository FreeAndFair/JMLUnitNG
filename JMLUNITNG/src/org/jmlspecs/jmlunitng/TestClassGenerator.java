package org.jmlspecs.jmlunitng;

public class TestClassGenerator implements Constants{

	public TestClassGenerator()
	{
		//Constructor
	}
	public void perform()
	{
		//Generates the Test oracle class.
	}
	protected void generateTestClass()
	{
		// Generated the test oracle. Calls all other methods to generate oracle.
	}
	protected void printFileHeader() {
		 //Writes file header.
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
}

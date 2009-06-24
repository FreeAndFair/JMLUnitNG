package org.jmlspecs.jmlunitng;

import java.io.FileNotFoundException;
import java.util.Date;

import org.multijava.mjc.JClassDeclarationType;
import org.multijava.mjc.JClassOrGFImportType;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JPackageImportType;
import org.multijava.mjc.JTypeDeclarationType;

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
	
	/** Prints the import statements to the _JML_TEST file */
	protected void printImportStatements(JCompilationUnit cunit)
	 {
		JPackageImportType[] pkgs = cunit.importedPackages();
        boolean isFirstImport = true;
        
        for (int i = 0; i < pkgs.length ; i++) {
	            if (pkgs[i].getName().equals("java/lang")) {
	                continue;
	                }
	            if (isFirstImport) {
	              
	                isFirstImport = false;
	                }
	            writer.print("import " + pkgs[i].getName().replace('/', '.') + ".*;");
             }
        
        JClassOrGFImportType[] classes = cunit.importedClasses();
        
        for (int i = 0; i < classes.length ; i++) {
	            if (isFirstImport) {
	               
	                isFirstImport = false;
	                }
	            writer.print("import " + classes[i].getName().replace('/', '.') + ";");
            }

        if (PKG_JUNIT.length() == 0) {
            if (isFirstImport) {
                
                isFirstImport = false;
            	}
            writer.print("import junit.framework.*;");
        	}
        if (PKG_JMLRAC.length() == 0) {
            if (isFirstImport) {
                
                isFirstImport = false;
            	}
            writer.print("import org.jmlspecs.jmlrac.runtime.*;");
        	}
        if (PKG_JMLUNITNG.length() == 0) {
            if (isFirstImport) {
               
                isFirstImport = false;
            	}
            writer.print("import org.jmlspecs.jmlunitng.*;");
        	}
	 }
	/** This method prints the Javadoc comment for the _JML_Test class */
	protected void printClassJavadoc ()
	{
		String name = typeDeclaration.ident();
        writer.print("/** Automatically-generated test driver"
                + " for JML and JUnit based");
        writer.print(" * testing of " + name
                + ". The superclass of this class should be edited");
        writer.print(" * to supply test data."
                + " However it's best not to edit this class");
        writer.print(" * directly; instead use the command");
        writer.print(" * <pre>");
        writer.print(" *  jmlunit " + name + ".java");
        writer.print(" * </pre>");
        writer.print(" * to regenerate this class whenever "
                + name + ".java changes.");
        writer.print(" */");
	}
	
	/** Generates the Test Class Name */
	protected void generateTestClassName(JTypeDeclarationType cdecl)
	{
		this.typeDeclaration = cdecl;
        testClassName = cdecl.ident() + TEST_CLASS_NAME_POSTFIX;
	}
	
	/** Print the Class header for _JML_Test class */
	protected void printClassHeader(){
			writer.print("public ");
			writer.print("class " + testClassName);
	        writer.newLine();
	        writer.print(" extends " + testClassName + "Data");
	        writer.newLine();
	        writer.print("{");
	}
	protected void initializeFixture()
	{
		//Initialize the parameters.
	}
	/** Print the Constructor for the class _JML_Test */
	protected void printConstructor() {
		writer.newLine();     
		writer.print("public "+ testClassName + "() {" );
		writer.newLine();
		writer.print("super();");
		writer.newLine();
		writer.print("}");
	 }
	/** Print the main method to run the tests */
	protected void printMain() {
		writer.newLine();
		writer.print("/** Run the tests. */");
		writer.newLine();
        writer.print("public static void main(java.lang.String[] args) {");
        writer.newLine();
        writer.print("org.jmlspecs.jmlunit.JMLTestRunner.run(suite());");
        writer.newLine();
        writer.print("}");
	}
	protected void printSuite() {
		
	}
	private void printTestIsRACCompiled(JTypeDeclarationType cdecl){
		
		String cname = cdecl.ident();
        String whatKind_space;
        if (cdecl instanceof JClassDeclarationType) {
            whatKind_space = "class ";
        } else {
            whatKind_space = "interface ";
        }
        writer.newLine(); 
        writer.print("/** Test to see if the code for ");
        writer.print(whatKind_space);
        writer.print(cname);
        writer.print(" * has been compiled with runtime assertion checking" +
                " (i.e., by jmlc).");
        writer.print(" * Code that is not compiled with jmlc would not make" +
                " an effective test,");
        writer.print(" * since no assertion checking would be done." +
                " */");
        
        writer.print("public void test$IsRACCompiled() {");
        writer.newLine();

        writer.print(PKG_JUNIT + "Assert.assertTrue(\"code for ");
        writer.print(whatKind_space);
        writer.print(cname);
        writer.print("\"");
        writer.newLine();
        writer.newLine();
        writer.print("+ \" was not compiled with jmlc\"");
        writer.print("+ \" so no assertions will be checked!\",");
        writer.newLine();
        writer.print(PKG_JMLRAC + "JMLChecker.isRACCompiled(" + cname + ".class)");
        writer.print(");");
        writer.newLine();

        writer.newLine();
        writer.print("}");
	}
	private boolean preconditionPass(){
		return true;
		//returns false if the precondition violation exception occurs. Need to throw PreconditionViolationSkipException. 
	}
	/*
	 * There are many other private and protected methods which I will need to create. One class need to be created for storing 
	 * parameters used by these methods.
	 */
	
	
//	public static void main(String[] args) throws FileNotFoundException
//	{
//		TestClassGenerator t = new TestClassGenerator(); 
//		t.printFileHeader();
//	}
    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
	
	private Writer writer;
	
	private JTypeDeclarationType typeDeclaration;
	
	private String testClassName;
}

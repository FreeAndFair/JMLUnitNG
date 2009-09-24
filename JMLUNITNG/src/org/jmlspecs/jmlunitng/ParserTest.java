package org.jmlspecs.jmlunitng;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.jmlunit.JntOptions;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MjcCommonOptions;
import org.multijava.mjc.ParsingController.ConfigurationException;

import antlr.RecognitionException;
import antlr.TokenStreamException;

public class ParserTest
{

  /**
   * @param args
   * @throws ConfigurationException 
   * @throws TokenStreamException 
   * @throws RecognitionException 
   * @throws FileNotFoundException 
   */
  public static void main(String[] args) throws FileNotFoundException, RecognitionException, TokenStreamException, ConfigurationException
  {
   File file = new File(args[0]);
   final MjcCommonOptions my_options = new JntOptions("jmlunitng");
   MJClassParser parser = new MJClassParser(file, my_options);
   JCompilationUnit j_type = (JCompilationUnit) parser.parse(true, true, true, true, "jmlunit");
   JTypeDeclarationType[] decl = j_type.typeDeclarations();
   List<Object> methods = decl[0].methods();
   CSourceClass[] sc = j_type.allTypeSignatures();
   for(int i = 0; i < sc.length; i++)
   {
      ArrayList list = null;
     sc[i].getAllMethods(list);
     for(Object k : list)
     {
       if (k instanceof JMethodDeclaration)
       {
         JMethodDeclaration mth = (JMethodDeclaration)k;
        
        // System.out.println(decl[0].modifiers());
         System.out.println(mth.ident() + " " + mth);
       }
     }
   }
   for(Object m : methods)
   {
   
   
    if (m instanceof JMethodDeclaration)
    {
      JMethodDeclaration mth = (JMethodDeclaration)m;
     
     // System.out.println(decl[0].modifiers());
      System.out.println(mth.ident() + " " + mth);
    }
   }

  }

}

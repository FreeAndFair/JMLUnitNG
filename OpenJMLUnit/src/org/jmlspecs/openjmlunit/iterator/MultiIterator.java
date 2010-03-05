/*
 * OpenJMLUnit
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "OpenJML"
 * @creation_date "March 2010"
 * @last_updated_date "March 2010"
 * @keywords "unit testing", "JML"
 */

package org.jmlspecs.openjmlunit.iterator;

/**
 * A repeated access iterator that combines one or more other iterators.
 * 
 * @author Daniel M. Zimmerman
 * @version March 2010
 */
public class MultiIterator implements RepeatedAccessIterator {
  // Commands
  
  // @command "Embed the_list_of_iterators into a single iterator!"
  
  // Constraints
  
  // @constraint "The sequence of elements returned is exactly the
  //              concatenation of the sequences of elements returned by
  //              the iterators in the iterator list, in the order they
  //              appear in the list."
}

package bobj;

import java.util.*;

public class SingleSubstitution {

   private Variable var;
   private Term term;

   public SingleSubstitution(Variable var, Term term) {
      this.var = var;
      this.term = term;
   }


   public Variable getVariable() {
      return var;
   }

   public Term getTerm() {
      return term;
   }

}

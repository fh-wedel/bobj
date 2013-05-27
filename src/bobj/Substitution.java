
package bobj;

import java.io.*;
import java.util.*;

public class Substitution implements Serializable {

   private Hashtable substs;

   public Substitution() {
      substs = new Hashtable();
   }

   public void addSubst(Variable v, Term t) throws SubstitutionException {

      if (!v.getSort().equals(t.getSort())) {
         throw new SubstitutionException();          
      }

      boolean found = false;
      Enumeration e = substs.keys();
      Hashtable table = new Hashtable();
      while (e.hasMoreElements() && ! found ) {
          Variable tmp = (Variable)e.nextElement();
          if (tmp.equals(v)) {
              found = true;
          } else {

              Term term = (Term)substs.get(tmp);
              term = term.subst(v, t);
              table.put(tmp, term);
          }
      } 
      if (found) {
          throw new SubstitutionException();
      } else {
          table.put(v,t);
      }

      substs = table;
   }



   public void addSubst(Variable v, Term t, Signature sig)
       throws SubstitutionException {

      if (!sig.isSubsort(t.getSort(), v.getSort())) {
         throw new SubstitutionException();          
      }

      boolean found = false;
      Enumeration e = substs.keys();
      Hashtable table = new Hashtable();
      while (e.hasMoreElements() && ! found ) {
          Variable tmp = (Variable)e.nextElement();
          if (tmp.equals(v)) {
              found = true;
          } else {

              Term term = (Term)substs.get(tmp);
              term = term.subst(v, t);
              table.put(tmp, term);
          }
      } 
      if (found) {
          throw new SubstitutionException();
      } else {
          table.put(v,t);
      }

      substs = table;
   }



    
   public void add(Substitution sub) throws SubstitutionException {

       SingleSubstitution[] all = sub.getAll();
       for (int i=0; i<all.length; i++) {
          Variable var = all[i].getVariable();
          Term term = all[i].getTerm();
          addSubst(var, term);
       }

   }



   public SingleSubstitution[] getAll() {

     Vector pool = new Vector();

     Enumeration e = substs.keys();
     while (e.hasMoreElements()) {
        Variable var = (Variable)e.nextElement();
        Term term = (Term)substs.get(var);
        pool.addElement(new SingleSubstitution(var, term));

     }

     SingleSubstitution[] result = new SingleSubstitution[pool.size()];
     pool.copyInto(result);

     return result;
   }


   public Term get(Variable var) {

      Term result = new Term(var);

      Enumeration e = substs.keys();
      while (e.hasMoreElements()) {
         Variable vtmp = (Variable)e.nextElement();
         if (var.equals(vtmp)) {
	     result = (Term)substs.get(vtmp);
	     return result;
         }
      }

      return result;

   }


   public boolean contains(Variable var) {

     boolean result = false;
     Enumeration e = substs.keys();
     while (e.hasMoreElements()) {
         Variable vtmp = (Variable)e.nextElement();
         if (var.equals(vtmp)) {
	     return true;
         }
     }

     return result;

   }


   public String toString() {
     String result = "";
     Enumeration e = substs.keys();
     while (e.hasMoreElements()) {
        Variable var = (Variable)e.nextElement();
        Term term = (Term)substs.get(var);
        if (result.equals("")) {
          result += var+" -> "+term;
        } else {
          result += ", "+var+" -> "+term;
        }
     }
     return "{"+result+"}";
   }
   
}

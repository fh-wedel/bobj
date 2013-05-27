
package bobj;

import java.io.*;
import java.util.*;

public class Equation  implements Serializable {

    protected Term left;
    protected Term right;
    protected Term condition;
    protected String info;
    protected String name;
    static boolean debug = false;
        
    public Equation(Term l, Term r) {
	left = l;
	right = r;
	info = "";
    }

    public Equation(Term c, Term l, Term r) {
	condition = c;
	left = l;
	right = r;
	info = "";
    }
    
    public boolean equals(Object obj) {

	if (debug) {
	    System.out.println("------------equation equals --------------");
	    System.out.println(this+"     "+obj);
	}


	if (!(obj instanceof Equation)) {
	    return false;
	}

	Equation eq = (Equation)obj;
	if  (left.equals(eq.left) && right.equals(eq.right)) {

	    if (debug) {
		System.out.println("-------------------");
		System.out.println("yes. they are same");
		System.out.println("-------------------");
		System.out.println(this.condition);
		System.out.println(eq.condition);
	    }
	    	    
	    if (isConditional() &&
		eq.isConditional() &&
		condition.equals(eq.condition)) {
		return true;
	    } else if (!isConditional() && !eq.isConditional()){
		return true;
	    }	    
	}


        // try a new method
        /*
	HashMap map = new HashMap();
	if (left.shift().equals(eq.left, map) && right.shift().equals(eq.right, map)) {

	    if (debug) {
		System.out.println("-------------------");
		System.out.println("yes again. they are same again");
		System.out.println("-------------------");
		System.out.println(this.condition);
		System.out.println(eq.condition);
		System.out.println(map);
	    }
	    
	    if (isConditional() &&
		eq.isConditional() &&
		condition.equals(eq.condition, map)) {

		System.out.println("bbb: "+this+"  \n      "+eq );

		return true;
	    } else if (!isConditional() && !eq.isConditional()) {
		return true;
	    } 
	}
	*/
		
	return false;
    }


    public Term getCondition() {
	return condition;
    }


    public Term getLeft() {
	return left;
    }
  
    public Term getRight() {
	return right;
    }


    public boolean isConditional() {
	return (condition != null);
    }


    public void setInfo(String info) {
	this.info = info;
    }


    public String getInfo() {
	return info;
    }


    public String toString() {

	String result = "";

	if (name != null) {
	    result += "["+name+"] ";
	}
		
	if (isConditional()) {
	    result += "cq "+getLeft()+" = "+getRight()+" if "+getCondition();
	} else {
	    result += "eq "+getLeft()+" = "+getRight();
	}

	return result;

    }


    public Equation subst(Signature sig, Variable var, Term term) {

	Term c = null;
	if (condition != null) {
	    c = condition.subst(sig,var,term);
	}
	Term l = left.subst(sig,var,term);
	Term r = right.subst(sig,var,term);

	Equation eq = new Equation(c,l,r);
	if (name != null) {
	    eq.name = name;
	}
	return eq;

    }


    public Equation subst(Variable var, Term term) {

	Term c = null;
	if (condition != null) {
	    c = condition.subst(var,term);
	}
	Term l = left.subst(var,term);
	Term r = right.subst(var,term);

	Equation eq = new Equation(c,l,r);
	if (name != null) {
	    eq.name = name;
	}
	return eq;	   

    }


    public Equation addAnnotation(String name, Signature sig, Map env) {

	Term l = left.addAnnotation(name, sig, env);
	Term r = right.addAnnotation(name, sig, env);
	if (condition != null) {
	    Term c = condition.addAnnotation(name, sig, env);
	    Equation eq = new Equation(c, l, r);
	    if (this.name != null) {
		eq.name = this.name;
	    }
	    eq.info = info;
	    return eq;	    
	} else {
	    Equation eq = new Equation(l, r);
	    if (this.name != null) {
		eq.name = this.name;
	    }
	    eq.info = info;
	    return eq;
	}

    }


    public Equation removeAnnotation(String name, Signature sig) {

	Term l = left.removeAnnotation(name, sig);
	Term r = right.removeAnnotation(name, sig);
	if (condition != null) {
	    Term c = condition.removeAnnotation(name, sig);
	    Equation eq = new Equation(c, l, r);
	    if (this.name != null) {
		eq.name = this.name;
	    }
	    eq.info = info;
	    return eq;
	} else {
	    Equation eq = new Equation(l, r);
	    if (this.name != null) {
		eq.name = this.name;
	    }
	    eq.info = info;
	    return eq;
	}

    }



    public Equation changeSort(Sort olds, Sort news, Signature sig) {
	
	Term l = left.changeSort(olds, news, sig);
	Term r = right.changeSort(olds, news, sig);
	if (condition != null) {
	    Term c = condition.changeSort(olds, news, sig);
	    Equation eq = new Equation(c, l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	} else {
	    Equation eq = new Equation(l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	}	

    }



    public Equation changeModuleName(ModuleName olds,
				     ModuleName news,
				     Signature sig) {

	Term l = left.changeModuleName(olds, news, sig);
	Term r = right.changeModuleName(olds, news, sig);
	if (condition != null) {
	    Term c = condition.changeModuleName(olds, news, sig);
	    Equation eq = new Equation(c, l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	} else {
	    Equation eq = new Equation(l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	}

    }



    public Equation changeAbsoluteModuleName(ModuleName olds,
					     ModuleName news,
					     Signature sig) {

	Term l = left.changeAbsoluteModuleName(olds, news, sig);
	Term r = right.changeAbsoluteModuleName(olds, news, sig);
	if (condition != null) {
	    Term c = condition.changeAbsoluteModuleName(olds, news, sig);
	    Equation eq = new Equation(c, l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	} else {
	    Equation eq = new Equation(l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	}

    }


    public Equation changeParameterName(String olds,
					String news,
					Signature sig) {

	Term l = left.changeParameterName(olds, news, sig);
	Term r = right.changeParameterName(olds, news, sig);
	if (condition != null) {
	    Term c = condition.changeParameterName(olds, news, sig);
	    Equation eq = new Equation(c, l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	} else {
	    Equation eq = new Equation(l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	}

    }
    

    public Equation replaceOperationName(String oldname,
					 String newname,
					 Signature sig) {

	Term l = left.replaceOperationName(oldname, newname, sig);
	Term r = right.replaceOperationName(oldname, newname, sig);
	if (condition != null) {
	    Term c = condition.replaceOperationName(oldname, newname, sig);
	    Equation eq = new Equation(c, l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	} else {
	    Equation eq = new Equation(l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	}

    }


    public Equation changeOperation(Operation from,
				    Operation to,
				    Signature sig) {

	Term l = left.changeOperation(from, to, sig);
	Term r = right.changeOperation(from, to, sig);
	if (condition != null) {
	    Term c = condition.changeOperation(from, to, sig);
	    Equation eq = new Equation(c, l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	    
	} else {
	    Equation eq = new Equation(l, r);
	    if (name != null) {
		eq.name = name;
	    }
	    eq.info = info;
	    return eq;
	}

    }


    public void setName(String name) 
    {
	this.name = name;
    }


    public String getName() 
    {
	return name;
    }
    
}



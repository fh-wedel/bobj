
package bobj;

import java.util.*;
import java.io.*;

public class ReducedTerm {

    private Operation operation;
    private ReducedTerm[] subterms;
    private Variable var;

    private Hashtable helper;
    private Sort[] retract;
    private ReducedTerm parent;

    private ReducedTerm target;   // matched an equation?
    private Module module;

    public ReducedTerm(Term term, Module module) {

	this.module = module;

	operation = term.getTopOperation();
	if (term.getSubterms() != null) {
	    subterms = new ReducedTerm[term.getSubterms().length];
	    for (int i=0; i<subterms.length; i++) {
		subterms[i] = new ReducedTerm((term.getSubterms())[i], module);
		subterms[i].parent = this;
	    }
	}
	var = term.getVariable();
	retract = term.getRetract();

	// handle the information about module
	Equation[] eqs = (Equation[])(module.equations.toArray());
	Hashtable op2eq = new Hashtable();

	for (int i=0; i<eqs.length; i++) {
	    Term left = eqs[i].getLeft();
	    if (left.getTopOperation() != null) {
		Vector tmp = (Vector)op2eq.get(left.getTopOperation().getName());
		if (tmp == null)
		    tmp = new Vector();
		tmp.addElement(eqs[i]);
		op2eq.put(left.getTopOperation().getName(), tmp);
	    }
	}

	Vector conside = new Vector();
	if (operation != null) {    
	    conside = (Vector)op2eq.get(operation.getName());
	}

	//System.out.println("\n======== conside for term "+term);
	//System.out.println(conside);

	if (conside == null) {
	    conside = new Vector();
	}

	for (int i=0; i<conside.size(); i++) {
	    Equation eq = (Equation)conside.elementAt(i);
	    Term left = eq.getLeft();
	    Term right = eq.getRight();
	    Term cond = eq.getCondition();

	    Hashtable var2term = getMatch(term, left);

	    //System.out.println("what ==== "+var2term);

	    if (var2term != null ) {
		Enumeration e = var2term.keys();
		while (e.hasMoreElements()) {
		    Variable var = (Variable)e.nextElement();
		    Term trm = (Term)var2term.get(var);
		    right = right.subst(var, trm);
		}

		//System.out.println("--------- "+right);
		target = new ReducedTerm(right, module);
		break;
	    }
     
	}

    }


    private static Hashtable getMatch(Term term, Term pattern) {


	//System.out.println("\n------ match -------");
	//System.out.println(term);
	//System.out.println(pattern);

	Hashtable result = new Hashtable();

	if (pattern.isVariable()) {
	    result.put(pattern.getVariable(), term);
	} else if (term.getTopOperation() == null) {
	    return null;
	} else if (term.getTopOperation().equals(pattern.getTopOperation())) {
	    Term[] subterms = term.getSubterms();
	    Term[] subpatterns = pattern.getSubterms();
	    for (int i=0; i<subterms.length; i++) {
		Hashtable tmp = getMatch(subterms[i], subpatterns[i]);
		if (tmp == null) {
		    return null;
		} else {
		    Enumeration e = tmp.keys();
		    while (e.hasMoreElements()) {
			Variable var = (Variable)e.nextElement();
			Term trm1 = (Term)tmp.get(var);
			Term trm2 = (Term)result.get(var);
			if (trm2 == null) {
			    result.put(var, trm1);
			} else if (!trm1.equals(trm2)) {
			    return null;
			}
		    }
		}
	    }
	} else {
	    result = null;
	}

	return result;
    }



    public Term toTerm() {

	Term result = null;

	if (var != null) {
	    result = new Term(var);
	} else {
	    Term[] terms = new Term[subterms.length];
	    for (int i=0; i<terms.length; i++) {
		terms[i] = subterms[i].toTerm();
	    }
	    try {
		result = new Term(operation, terms);
	    } catch (Exception e) {
		e.printStackTrace();
	    }
	}

	return result;
    }

    public String toString() {
	String result = "";

	if (var != null) {
	    result += var.getName();
	} else if (operation.isConstant()) {
	    result += operation.getName();
	} else if (operation.isMixNotation()) {

	    String tmp = operation.getName();
	    int i = tmp.indexOf("_");
	    int count = 0;
	    while (i != -1) {
		ReducedTerm t = subterms[count];
		String sub = t.toString().trim();

		if (t.subterms != null) {

		    Operation op = t.operation;
		    if (op.isMixNotation() && !op.getCleanName().equals("==")) {
			if (op.getCleanName().equals("and") ||
			    operation.getCleanName().equals("==")) {
			    sub = "("+sub+")";    // Nov.23
			} else if (operation.getPriority() > op.getPriority()) {
			    sub = "("+sub+")";    // Nov.23
			} else {
			    sub = "("+sub+")";
			}
		    };
		};

		count ++;
		tmp = tmp.substring(0,i).trim()+" "+sub
		    +" "+tmp.substring(i+1).trim();
		i = tmp.indexOf("_");
	    };
	    result += tmp;

	} else {
	    result += operation.getName()+"(";
	    for (int i=0; i<subterms.length; i++) {
		result += subterms[i].toString();
		if (i < subterms.length-1) {
		    result += " , ";
		};
	    };
	    result += ")";
	};
	return result.trim();
    }


    public ReducedTerm getNormalForm() { 

	ReducedTerm term = this;
	Redex[] redex = term.getRedex();

	while (redex != null && redex.length != 0 ) {
	    for (int i=0; i<redex.length; i++) {
		term =  term.replaceAt(redex[i].getPoint(), redex[i].getTerm());
	    }
	    redex = term.getRedex();
	}

	return term;
    }


    public Redex[] getRedex() {
	if (target != null) {
	    Redex[] redex = { new Redex(this, target)};
	    return redex;
	} else {
	    if (subterms != null && subterms.length != 0) {
		Vector pool = new Vector();
		for (int i=0; i<subterms.length; i++) {
		    Redex[] tmp =  subterms[i].getRedex();
		    for (int j=0; j < tmp.length; j++) {
			pool.addElement(tmp[j]);
		    }
		}
		Redex[] redex = new Redex[pool.size()];
		pool.copyInto(redex);
		return redex;
	    } else {
		return new Redex[0];
	    }
	}
    }

    public ReducedTerm replaceAt(ReducedTerm point, ReducedTerm term) { 

	//System.out.println("\n-----------------------------");
	//System.out.println("current: "+this);
	//System.out.println("point: "+point);
	//System.out.println("target: "+term);

	if (point.parent == null) {
	    System.out.println("result: "+term);
	    return term;
	} else {
	    ReducedTerm[] terms = point.parent.subterms;
	    for (int i=0; i<terms.length; i++) {
		if (terms[i] == point) {
		    terms[i] = term;
		    term.parent = point.parent;

		    point.parent.resetTarget();

		    break;
		}
	    }

	    // rebulit redex in the loacl area around point

	    //System.out.println("result: "+this);
     
	    return this;
	}
    }



    private void resetTarget() {

	System.out.println("\n--------- reset redex ----------");
	//System.out.println(this);

	if (target == null) {

	    // handle the information about module
	    Equation[] eqs = (Equation[])(module.equations.toArray());
	    Hashtable op2eq = new Hashtable();

	    for (int i=0; i<eqs.length; i++) {
		Term left = eqs[i].getLeft();
		if (left.getTopOperation() != null) {
		    Vector tmp = (Vector)op2eq.get(left.getTopOperation().getName());
		    if (tmp == null)
			tmp = new Vector();
		    tmp.addElement(eqs[i]);
		    op2eq.put(left.getTopOperation().getName(), tmp);
		}
	    }


	    Vector conside = new Vector();
	    if (operation != null) {    
		conside = (Vector)op2eq.get(operation.getName());
	    }

	    //System.out.println("\n======== conside for term "+term);
	    //System.out.println(conside);

	    if (conside == null) {
		conside = new Vector();
	    }

	    for (int i=0; i<conside.size(); i++) {
		Equation eq = (Equation)conside.elementAt(i);
		Term left = eq.getLeft();
		Term right = eq.getRight();
		Term cond = eq.getCondition();

		Hashtable var2term = getMatch(this.toTerm(), left);

		//System.out.println("what ==== "+var2term);

		if (var2term != null ) {
		    Enumeration e = var2term.keys();
		    while (e.hasMoreElements()) {
			Variable var = (Variable)e.nextElement();
			Term trm = (Term)var2term.get(var);
			right = right.subst(var, trm);
		    }

		    //System.out.println("find equation: "+eq);
		    //System.out.println("right: "+right);

		    target = new ReducedTerm(right, module);
		    break;
		}
     
	    }

	}

	System.out.println("------ done ------");
    }



    class Redex {

	ReducedTerm point;
	ReducedTerm term;

	public Redex(ReducedTerm point, ReducedTerm term) {
	    this.point = point;
	    this.term = term;
	}

	public ReducedTerm getPoint() {
	    return point;
	}

	public ReducedTerm getTerm() {
	    return term;
	}
    }

}

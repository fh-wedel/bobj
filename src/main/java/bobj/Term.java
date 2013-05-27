   
package bobj;

import java.util.*;
import java.io.*;

public class Term  implements Serializable {
   
    Operation operation;
    Term[] subterms;
    Variable var;

    Hashtable helper;
    Sort[] retract;
    Sort sort;

    Term parent;
    boolean nocheck = false;
    boolean nogcheck = false;
    boolean noscheck = false;
    boolean hasRetract = false;

    static boolean debug = false;
    static boolean showRetract = true;
        
    protected Term() {}

    public Term(Variable v) {
	var = v;
	helper = new Hashtable();

	retract = new Sort[1];
	retract[0] = null;
	sort = v.sort;
    }

    public Sort getSort() {
	return sort;
    }


    public Term(Signature sig, Operation op, Term[] args) 
	throws TermException {      
	    
	if (op.getArity() == args.length) {

	    // check the consistence between o and args
	    Sort[] s = op.argumentSorts;
	    retract = new Sort[s.length];

	    for (int i=0; i<s.length; i++) {
	  
		if (sig == null) {
		    
		    if (args[i].getSort().equals(s[i])) {
			retract[i] = null;
		    } else {
			throw new TermException("The "+i+"-th arguments of "+
						op.getName()+" should be "+
						s[i].getName()+".");
		    }
		    
		} else {
		    
		    if (sig.isSubsort(args[i].getSort(), s[i]) ) {
			retract[i] = null;
		    } else if (sig.isSubsort(s[i], args[i].getSort())) {
			retract[i] = s[i];
		    } else {
			Sort tmp = sig.canApply(s[i], args[i].getSort());
			if (tmp != null) {
			    retract[i] = tmp;
			} else {

			    Sort[] s1 = sig.getDirectSupersorts(s[i]);
			    Sort[] s2 = sig.getDirectSupersorts(args[i].getSort());
			    if (s1.length == 1 && s2.length == 1 &&
				s1[0].equals(s1[0])) {
				retract[i] = s[i];
			} else {
				throw new TermException("The "+i+
							"-th arguments of "+
							op.getName()+
							" should be "+
							s[i].getName()+".");
			    }
			    
			}
		    }
		}
		
		hasRetract = hasRetract || args[i].hasRetract;

	    }

	    operation = op;
	    subterms = args;
	    helper = new Hashtable();

	    for (int i=0; i<args.length; i++) {
		args[i].parent = this;
	    }

	    sort = op.resultSort;

	    if (op.info.equals("system-retract")) {
		hasRetract = true;
	    }

	} else {
	    throw new TermException(op.getName()+" expects "+op.getArity()+
				" arguments.");
	}
    }


    public Term(Operation op, Term[] args) throws TermException {
	this(null, op, args);
    }

    public Term(Operation op) throws TermException {
	this(null, op, new Term[0]);
    }


    public Term copy() {
	return copy(null);
    }
    
    
    public Term copy(Signature sig) {
	if (var != null) {
	    return new Term(var);
	} else {
	    Term[] terms = new Term[subterms.length];
	    for (int i=0; i<terms.length; i++) {
		terms[i] = subterms[i].copy(sig);
	    }
	    try {
		if (sig != null) 
		    return new Term(sig, operation, terms);
		else
		    return new Term(operation, terms);
	    } catch (Exception e) {
		return null;
	    }  
	}      
    }
    

    public Term[] getSubterms() {
	return subterms;
    }

    public Variable getVariable() {
	return var;
    }

    public boolean isVariable() {
	return (var != null);
    }


    public boolean isConstant() {
	return  (operation != null && operation.isConstant());
    }

    public Operation getTopOperation() {
	return operation;
    }


    protected Sort[] getRetract() {
	return retract;
    }


    public void setProperty(Object index, Object obj) {
	helper.put(index,obj);
    }


    public Object getPropertyBy(Object index) {
	return helper.get(index);
    }

    
    public Object removePropertyBy(Object index) {
	return helper.remove(index);
    }    

    public boolean equals(Object obj) {

	if (!(obj instanceof Term)) {
	    return true;
	}
	
	Term term = (Term)obj;
	boolean result = true;;
	if (this.isVariable() && term.isVariable()) {
	    result = this.getVariable().equals(term.getVariable());
	} else if (!this.isVariable() && !term.isVariable()) {
	    Operation op1 = this.getTopOperation();
	    Operation op2 = term.getTopOperation();
	    if (op1.equals(op2)) {
		if (op1.isAssociative() && !op1.isCommutative()) {
		    try {
			Vector v1 = this.getAssocSubterms(op1);
			Vector v2 = term.getAssocSubterms(op2);

			if (v1.size() == v2.size()) {
			    boolean same = true;
			    for (int i=0; i<v1.size(); i++) {
				Term tm1 = (Term)v1.elementAt(i);
				Term tm2 = (Term)v2.elementAt(i);
				same = same && tm1.equals(tm2);
			    }
			    result = same;
			} else {
			    result = false;
			}
		    } catch (TermException e) {}

		} else if (op1.isAssociative() && op1.isCommutative()) {

		    try {
			Vector v1 = this.getAssocSubterms(op1);
			Vector v2 = term.getAssocSubterms(op2);

			if (v1.size() == v2.size()) {
			    boolean same = true;
			    for (int i=0; i<v1.size(); i++) {
				Term tm1 = (Term)v1.elementAt(i);
				boolean found = false;
				for (int j=0; j<v2.size(); j++) {
				    Term tm2 = (Term)v2.elementAt(j);
				    if (tm1.equals(tm2)) {
					v2.remove(tm2);
					found = true;
					break;
				    }
				}
				if (!found) {
				    same = false;
				    break;
				}
			    }
			    result = same;
			} else {
			    result = false;
			}
		    } catch (TermException e) {}

		} else {
		    
		    Term[] tm1 = this.getSubterms();
		    Term[] tm2 = term.getSubterms();
		    boolean same = true;
		    for (int i=0; i<tm1.length; i++) {
			same &= tm1[i].equals(tm2[i]);
		    }
		    result = same;
		}
	    } else {
		result = false;
	    }
	} else {
	    result = false;
	}

	return result;
    }


    public boolean equals(Signature sig, Term term) {

	
	boolean result = true;
	if (this.isVariable() && term.isVariable()) {
	    result = this.getVariable().equals(term.getVariable());
	} else if (!this.isVariable() && !term.isVariable()) {
	    Operation op1 = this.getTopOperation();
	    Operation op2 = term.getTopOperation();

	    if (op1.equals(op2) || op1.less(sig, op2) || op2.less(sig, op1)) {
		
		if (op1.isAssociative() && !op1.isCommutative()) {
	   	    
		    boolean okay = true;
		    if (sort.isHidden()) {
			Term tmp = this.parent;
			while (tmp != null) {
			    if (tmp.operation.isBehavorial()) {
				tmp = tmp.parent;
			    } else {
				okay = false;
				break;
			    }
			}
		    }

		    if (okay) {

			try {
			    Vector v1 = this.getAssocSubterms(sig, op1);
			    Vector v2 = term.getAssocSubterms(sig, op2);

			    if (v1.size() == v2.size()) {
				boolean same = true;
				for (int i=0; i<v1.size() && same; i++) {
				    Term tm1 = (Term)v1.elementAt(i);
				    Term tm2 = (Term)v2.elementAt(i);
				    same &= tm1.equals(sig, tm2);
				}

				if (!same) {
				    result = false;
				}

			    } else {
				result = false;
			    }

			} catch (TermException e) {}

		    } else {
			result =
			    this.subterms[0].equals(sig, term.subterms[0]) &&
			    this.subterms[1].equals(sig, term.subterms[1]) ;
		    }

		} else if (op1.isAssociative() && op1.isCommutative()) {
		    		    
		    boolean okay = true;
		    if (sort.isHidden()) {
			Term tmp = this.parent;
			while (tmp != null) {
			    if (tmp.operation.isBehavorial()) {
				tmp = tmp.parent;
			    } else {
				okay = false;
				break;
			    }
			}
		    }
	
		    if (okay) {

			try {
			    Vector v1 = this.getAssocSubterms(sig, op1);
			    Vector v2 = term.getAssocSubterms(sig, op2);

			    if (v1.size() == v2.size()) {
				for (int i=0; i<v1.size() && result; i++) {
				    Term tm1 = (Term)v1.elementAt(i);

				    boolean found = false;
				    for (int j=0; j<v2.size(); j++) {
					Term tm2 = (Term)v2.elementAt(j);
					if (tm1.equals(sig, tm2)) {
					    v2.removeElementAt(j);
					    found = true;
					    break;
					}
				    }

				    if (!found) {
					result = false;
					break;
				    }
				}

			    } else {
				result = false;
			    }

			} catch (TermException e) {}

		    } else {
			result =
			    this.subterms[0].equals(sig, term.subterms[0]) &&
			    this.subterms[1].equals(sig, term.subterms[1]) ;
		    }

		} else if (op1.isCommutative()) {

		    result = this.subterms[0].equals(sig, term.subterms[0]) &&
			this.subterms[1].equals(sig, term.subterms[1]) ;

		    if (!result) {

			boolean okay = true;
			if (sort.isHidden()) {
			    Term tmp = this.parent;
			    while (tmp != null) {

				if (tmp.operation.isBehavorial()) {
				    tmp = tmp.parent;
				} else {
				    okay = false;
				    break;
				}
			    }
			}

			if (okay)
			    result =
			      this.subterms[0].equals(sig, term.subterms[1]) &&
			      this.subterms[1].equals(sig, term.subterms[0]) ;

		    }


		} else {

		    Term[] tm1 = this.getSubterms();
		    Term[] tm2 = term.getSubterms();
		    boolean same = true;
		    for (int i=0; i<tm1.length; i++) {
			same &= tm1[i].equals(sig,tm2[i]);
		    }
		    result = same;
		}
	    } else {
		result = false;
	    }
	} else {
	    result = false;
	}

	if (!result) {	
	    
	    if (sort.equals(BoolModule.boolSort) &&
		term.sort.equals(BoolModule.boolSort) &&
		sort.isDefault() &&
		term.sort.isDefault()) {
		
		try {
		    
		    Vector termlist = new Vector();
		    Term l = this.extract(termlist);

		    int len = termlist.size();
		    Term r = term.extract(termlist);
		    
		    if (len == termlist.size() &&
			(!l.equals(this) || !r.equals(term)) ) { 

			if (checkBoolEquality(l, r, len)) {    
			    result = true;
			}             
		    }
		} catch (Exception e) {
		    e.printStackTrace();
		}
	    }
	}


	return result;
    }



    private boolean checkBoolEquality(Term term1, Term term2, int len) {
      
	if (len == 0) {

	    boolean old = RewriteEngine.trace;
	    RewriteEngine.trace = false;
	    
	    term1 = BoolModule.bool.getNormalForm(term1);
	    term2 = BoolModule.bool.getNormalForm(term2);

	    RewriteEngine.trace = old;
	    return term1.equals(term2);
	} else {
	    try {
		
		Sort bool = BoolModule.boolSort;
		Operation trueOp = BoolModule.trueOp;
		Operation falseOp = BoolModule.falseOp;

		Term t = new Term(trueOp, new Term[0]);
		Term f = new Term(falseOp, new Term[0]);
		Variable var = new Variable("B"+(len-1), bool);

		Term l1 = term1.subst(var, t);
		Term r1 = term2.subst(var, t);
		
		if (checkBoolEquality(l1, r1, len-1)) {

		    Term l2 = term1.subst(var, f);
		    Term r2 = term2.subst(var, f);

		    return checkBoolEquality(l2, r2, len-1);

		} else {
		    return false;
		}
	    } catch (Exception e) {
		return false;
	    }
	}
    }


    public String toString() {
	String result = "";

	if (isVariable()) {
	    String tmp = var.name;
	    result += tmp;
	} else if (operation.isConstant()) {
	    result += operation.getName();
	} else if (operation.isMixNotation()) {

            if (operation.isAssociative() &&
		operation.getName().trim().startsWith("_") &&
		operation.getName().trim().endsWith("_")) {

		String mid = operation.getName().trim().substring(1);
		mid = mid.substring(0, mid.length()-1).trim();
		
	        Vector vec = null;
		try {
		    vec = this.getAssocSubterms(operation);
		} catch (Exception e){
		}
		for (int i=0; i<vec.size(); i++) {
		    Term t = (Term)vec.elementAt(i);
		    String sub = t.toFullString().trim();
		    if (t.isComposite() &&
			t.operation.isMixNotation()) {
			sub = "("+sub+")";
		    }
		    if (mid.length() == 0) {
                        result += sub+" ";
		    } else {
			result += sub+" "+mid+" ";
		    }
		}

		if (mid.length() != 0) {
		    return result.substring(0,
				     result.length()-mid.length()-2).trim();
		} else {
		    return result.trim();
		}
	    }

	    String tmp = operation.getName();
	    int i = tmp.indexOf("_");
	    int count = 0;
	    while (i != -1) {
		Term t = subterms[count];
		String sub = t.toString().trim();

		if (t.isComposite()) {
		    Operation op = t.getTopOperation();
		    if (op.isMixNotation() &&
			!op.getCleanName().equals("==")) {
			if (op.getCleanName().equals("and") ||
			    operation.getCleanName().equals("==")) {
			    //sub = "("+sub+")";    // Nov.23
			} else if (operation.getPriority() > op.getPriority()){
			    sub = "("+sub+")";    // Nov.23
			} else {
			    sub = "("+sub+")";
			}
		    }
		}

		count ++;

		String first = tmp.substring(0,i).trim();
		String second = tmp.substring(i+1).trim();

		if (!tmp.substring(0,i).trim().endsWith("[") &&
		    !tmp.substring(0,i).trim().endsWith("(")) {
		    first = first + " ";
		}
		
		if (!tmp.substring(i+1).trim().startsWith("]") &&
		    !tmp.substring(i+1).trim().startsWith(")")) {
		    		    
		    second = " "+second;
		    
		}
		
                tmp = first + sub + second;		
		i = tmp.indexOf("_");
		
	    }
	    result += tmp;

	} else {
	    result += operation.getName()+"(";
	    for (int i=0; i<subterms.length; i++) {
		result += subterms[i].toString();
		if (i < subterms.length-1) {
		    result += ", ";
		}
	    }
	    result += ")";
	}
	return result.trim();
    }



    
    public String toFullString() {

	String result = "";

	if (isVariable()) {
	    result += var.getName();
	} else if (operation.isConstant()) {
	    result += operation.getName();
	} else if (operation.isMixNotation()) {

	    if (operation.isAssociative() &&
		operation.getName().equals("_  _")) {
		try {
		    Vector terms = getAssocSubterms(operation);
		    for (int i=0; i<terms.size(); i++) {
			Term term = (Term)terms.elementAt(i);

			if (term.isComposite()) {
			    result += " ("+term.toString()+")";
			} else {
			    result += " "+term.toString();
			}
			    
		    }
		    return result.trim();			
		} catch (TermException e) {
		}
	    }

	    if (operation.isAssociative() &&
		operation.getName().equals("_ _")) {
		try {
		    Vector terms = getAssocSubterms(operation);
		    for (int i=0; i<terms.size(); i++) {
			Term term = (Term)terms.elementAt(i);

			if (term.isComposite()) {
			    result += " ("+term.toString()+")";
			} else {
			    result += " "+term.toString();
			}
			    
		    }
		    return result.trim();
		} catch (TermException e) {
		}
	    }

            if (operation.isAssociative() &&
		operation.getName().trim().startsWith("_") &&
		operation.getName().trim().endsWith("_")) {

		String mid = operation.getName().trim().substring(1);
		mid = mid.substring(0, mid.length()-1).trim();
		
	        Vector vec = null;
		try {
		    vec = this.getAssocSubterms(operation);
		} catch (Exception e){
		}
		for (int i=0; i<vec.size(); i++) {
		    Term t = (Term)vec.elementAt(i);
		    String sub = t.toFullString().trim();
		    if (t.isComposite() && t.operation.isMixNotation()) {
			sub = "("+sub+")";
		    }
		    result += sub+" "+mid+" ";
		}
		return result.substring(0,
					result.length()-mid.length()-2).trim();
				
	    }

            
	    
	    String tmp = operation.getName();
	    int i = tmp.indexOf("_");
	    int count = 0;
	    while (i != -1) {
		Term t = subterms[count];
		String sub = t.toFullString().trim();
		if (showRetract && retract[count] != null) { 
		    sub = "r:"+t.getSort().getName()+">"+
			retract[count].getName()+"("+sub+")";
		}

		if (t.isComposite()) {

		    Operation op = t.getTopOperation();
		    if (op.isMixNotation() &&
			!op.getCleanName().equals("==")) {
			if (op.getCleanName().equals("and") ||
			    operation.getCleanName().equals("==")) {
			    sub = "("+sub+")";    // Nov.23
			} else if (operation.getPriority() > op.getPriority()){

			    
			} else {
			    sub = "("+sub+")";    // Nov.23
			}
		    }
		}

		count ++;

		String first = tmp.substring(0,i).trim();
		String second = tmp.substring(i+1).trim();

		if (!tmp.substring(0,i).trim().endsWith("[") &&
		    !tmp.substring(0,i).trim().endsWith("(")) {
		    first = first + " ";
		}
		
		if (!tmp.substring(i+1).trim().startsWith("]") &&
		    !tmp.substring(i+1).trim().startsWith(")")) {
		    second = " "+second;
		    
		}

		tmp = first + sub + second;
		i = tmp.indexOf("_");
	    }
	    result += tmp;

	} else {
	    result += operation.getName()+"(";
	    for (int i=0; i<subterms.length; i++) {
		if (retract[i] == null || !showRetract ) {
		    result += subterms[i].toFullString();
		} else {
		    result += "r:"+subterms[i].getSort().getName()+">"+
			retract[i].getName()+"("+
			subterms[i].toFullString()+")";
		}
		if (i < subterms.length-1) {
		    result += ", ";
		}
	    }
	    result += ")";
	}
	return result.trim();
    }


    public String showStructure() {
	return showStructure("");
    }


    private String showStructure(String st) {
	String result = "";

	if (isVariable()) {
	    result += st+"var: "+var.getName()+"   "+
		var.getSort()+"\n";
	} else {

	    result += st+operation.toString().substring(2)+
		  "   "+operation.modName+"\n";
	    for (int i=0; i<subterms.length; i++) {
		result += st+subterms[i].showStructure(st+"  ");
	    }
	    
	}
	return result;
    }

        
    public String showStructure(Module module) {
	return showStructure(module, "");
    }


    private String showStructure(Module module, String st) {
		
	String result = "";

	if (isVariable()) {
	    result += st+module.toString(var)+"\n";
	} else {

	    result += st+module.toString(operation).substring(3)+"\n";
	    for (int i=0; i<subterms.length; i++) {
		result += subterms[i].showStructure(module, st+"  ");
	    }
	    
	}
	return result;
    }    

    public String showStructureWithModuleName(Module module) {
	return showStructureWithModuleName(module, "");
    }


    private String showStructureWithModuleName(Module module, String st) {
		
	String result = "";

	if (isVariable()) {
	    result += st+module.toString(var)+"\n";
	} else {

	    result += st+module.toString(operation).substring(3)+" in "+
		      operation.modName+"\n";
	    for (int i=0; i<subterms.length; i++) {
		result += subterms[i].showStructureWithModuleName(module,
								  st+"  ");
	    }
	    
	}
	return result;
    }    



    public static Term parse(Signature sig, String st) 
	throws TermException {

        String s = st;
	FastTermParser ftp = new FastTermParser(sig, s);
	ArrayList res = ftp.parse();
	
	if (res.size() == 0) {
	    String[] etks = ftp.getUnknownTokens();
	    String msg = "";
	    for (int i=0; i<etks.length; i++) {
		if (i < etks.length - 1)
		    msg += etks[i]+", ";
		else
		    msg += etks[i];
            }

	    if (msg.length() > 0) {
		msg = "Errors at the following token(s): "+msg;
		throw new TermException(
		   Module.format(msg+", when parsing \""+s.trim()+"\" ", 0));
	    } else {
		throw new TermException(
		   Module.format("No parse for "+s.trim(), 0));
	    }
	    
	    
	} else if (res.size() == 1) {	    
	    Term term = (Term)res.get(0);
	    return term;
	} else {
	    
	    // check whether something wrong there
	    res = checkPriority(res);
	    if (res.size() == 1) {
		return (Term)res.get(0);
	    }
	    
	    // check retraction
	    List list = checkRetract(res);
	    if (list.size() == 1) {
		return (Term)list.get(0);
	    }	    

	    // check default if_then_else_fi
	    list = checkDefaultIf(res);	    
	    if (list.size() == 1) {
		return (Term)list.get(0);
	    }		    

            // check whether overloading is possible
	    list = checkOverloading((Module)sig, res);
	    if (list.size() == 1) {
		Term result = (Term)list.get(0);
		return result;
	    }		 
	    
	    String msg = "multiple parsing results:\n";

	    Term term1 = (Term)res.get(0);
	    Term term2 = (Term)res.get(1);

	    String msg1 = term1.showStructure((Module)sig);
	    String msg2 = term2.showStructure((Module)sig);

            if (msg1.equals(msg2)) {
		msg += "------------------------------------------\n";
		msg += term1.showStructureWithModuleName((Module)sig);
		msg += "------------------------------------------\n";
		msg += term2.showStructureWithModuleName((Module)sig);
		msg += "------------------------------------------";
	    } else {
		msg += "------------------------------------------\n";
		msg += msg1;
		msg += "------------------------------------------\n";
		msg += msg2;
		msg += "------------------------------------------";
	    }
	    throw new TermException(msg, res.size());
	}
    
    }


    public static Term parse(Signature sig, String st, Sort expect) 
	throws TermException {
	
	String s = st;
    
	FastTermParser ftp = new FastTermParser(sig, s);
	ArrayList res = ftp.parse();
	
	Term possible = null;
	if (res.size() == 1) {
	    possible = (Term)res.get(0);
	}
	
        for (int i=res.size()-1; i>-1; i--) {
	    Term term = (Term)res.get(i);

	    if (!sig.less(term.sort, expect) &&
		!sig.less(expect, term.sort) &&
		!sig.hasCommonSubsort(expect, term.sort) &&
		!sig.hasCommonSupersort(expect, term.sort)) {
		
		res.remove(i);		
	    } 	    
	}
	
	if (res.size() == 0) {

	    if (possible != null) {
		throw new TermException(s+"is not on the sort "+
					expect.getName());
	    }

	    String[] etks = ftp.getUnknownTokens();
	    String msg = "";
	    for (int i=0; i<etks.length; i++) {
		if (i < etks.length - 1)
		    msg += etks[i]+", ";
		else
		    msg += etks[i];
		
            }

	    if (msg.length() > 0) {
		msg = "Errors at the following token(s): \""+msg+
		    "\", when parsing \""+s.trim()+"\" ";
		
		throw new TermException(Module.format(msg, 0));
	    } else {
		throw new TermException(
			      Module.format("No parse for "+s.trim()+" ", 0));
	    }
	    
	    
	} else if (res.size() == 1) {
	    
	    Term term = (Term)res.get(0);	
	    return term;
	    
	} else {
	    
	    // check whether something wrong there
	    res = checkPriority(res);	    
	    if (res.size() == 1) {
		return (Term)res.get(0);
	    }

	    // check retraction
	    List list = checkRetract(res);
	    if (list.size() == 1) {
		return (Term)list.get(0);
	    }	    

	    // check default if_then_else_fi
	    list = checkDefaultIf(res);	    
	    if (list.size() == 1) {
		Term result = (Term)list.get(0);
		return result;
	    }		    

            // check whether overloading is possible
	    list = checkOverloading((Module)sig, res);
	    if (list.size() == 1) {
		Term result = (Term)list.get(0);
		return result;
	    }		 
	    	    
	    String msg = "multiple parsing results:\n";
	    Term t1 = (Term)res.get(0);
	    Term t2 = (Term)res.get(1);

            msg += "------------------------------------------\n";
	    String m1 = t1.showStructure((Module)sig);
	    String m2 = t2.showStructure((Module)sig);
	    if (m1.equals(m2)) {
		m1 = t1.showStructureWithModuleName((Module)sig);
		m2 = t2.showStructureWithModuleName((Module)sig);
	    }
	    msg += m1+"------------------------------------------\n"+m2;
	    msg += "------------------------------------------";
	    throw new TermException(msg, res.size());
	}

    }


    private static ArrayList checkOverloading(Module module, ArrayList list)
    {
	
	ArrayList result = new ArrayList();

	Term res = null;
	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);

	    if (res == null) {
		res = term;
	    } else if (term.laterThan(module, res)) {
		res = term;
	    } else if (res.laterThan(module, term)) {
			    
	    } else {
		result.add(term);
		break;
	    }
	    
	}
	result.add(res);
	
	return result;	
    }
        

    private boolean laterThan(Module module, Term term) {
	
	if (this.var != null) {
	    return false;
	} else if (term.var != null) {
	    if (this.operation.resultSort.equals(term.var.sort)) {
		return true;
	    } else {
		return false;
	    }
	} else {

	    if (this.operation.name.equals(term.operation.name) &&
	        this.operation.resultSort.equals(term.operation.resultSort) &&
		this.operation.argumentSorts.length ==
		term.operation.argumentSorts.length ) {
				
		for (int i=0; i<this.operation.argumentSorts.length; i++) {
		    if (!this.operation.argumentSorts[i].equals(
		       term.operation.argumentSorts[i])) {
			return false;
		    }
		}
		
		if (module.modName.equals(this.operation.modName) &&
		      !module.modName.equals(term.operation.modName)) {

		    for (int i=0; i<this.operation.argumentSorts.length; i++) {

			if (this.subterms[i].laterThan(module,
						       term.subterms[i]) ||
			    this.subterms[i].equals(term.subterms[i])) {
			    
			} else {
			    return false;
			}
		    }

		    return true;
		    
		} else if (operation.modName.equals(term.operation.modName)) {

		    boolean later = false;
		    for (int i=0; i<this.operation.argumentSorts.length; i++) {

			if (this.subterms[i].laterThan(module,
						       term.subterms[i])) {
			    later = true;
			} else if (this.subterms[i].equals(term.subterms[i])) {
			    
			} else {
			    return false;
			}
		    }

		    return later;
		    
		} else {
		    return false;
		}
		
	    } else {
		return false;
	    }
	}
    }
    
    
    private static ArrayList checkDefaultIf(ArrayList list) 
    {
		
	ArrayList result = new ArrayList();
	
	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    if (term.contains(BoolModule.metaIf)) {
		result.add(term);
	    }
	}
	    
	return result;
    }

       
    protected static ArrayList checkRetract(ArrayList list) 
    {
		
	ArrayList result = new ArrayList();
	
	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    if (!term.needRetract()) {
		result.add(term);
	    }
	}
	    
	return result;
    }
    

    
    protected static ArrayList checkPriority(ArrayList list) 
    {
		
	ArrayList result = new ArrayList();
	List pathes = getPathes(list);
	
	for (int i=0; i<pathes.size(); i++) {
	    ArrayList source = (ArrayList)pathes.get(i);
	    boolean okay = true;
	    for (int j=0; j<pathes.size(); j++) {

		if (j == i) continue;
				
		ArrayList target = (ArrayList)pathes.get(j);
		if (hasLessPriorities(target, source)) {
		    okay = false;
		    break;
		}
		
	    }

	    if (okay) {	
		result.add(list.get(i));
	    }
	    
	}


	
        // another checking
	ArrayList tmp = new ArrayList();
	for (int i=0; i<result.size(); i++) {

	    Term t1 = (Term)result.get(i);
	    Operation op1 = t1.getTopOperation();
	    	    
	    boolean okay = true;
	    for (int j=0; j<tmp.size(); j++) {
		Term t2 = (Term)tmp.get(j);
		Operation op2 = t2.getTopOperation();

		if (op1 != null &&
		    op2 != null) {

		    if (op1.priority < op2.priority) {
			// insert op1, remove op2
			tmp.remove(j);
			break;
		    } else if (op2.priority < op1.priority) {
			// ignore op1
			okay = false;
			break;
		    }
		    
		}
		
	    }

	    if (okay) {
		tmp.add(t1);
	    }
	    
	}
	
        result = tmp;
	
	return result;
    }
    


    private static boolean hasLessPriorities(ArrayList list1, ArrayList list2) 
    {

        boolean less = false;

        if (list1.size() != list2.size()) {
	    return false;
	}
	
	for (int i=0; i<list1.size(); i++) {
	    ArrayList l = (ArrayList)list1.get(i);
	    ArrayList r = (ArrayList)list2.get(i);

	    int min = Math.min(l.size(), r.size());
	    for (int j=0; j<min; j++) {
		int a = ((Integer)l.get(j)).intValue();
		int b = ((Integer)r.get(j)).intValue();
		if (a > b) {
		    return false;
		} else if (a < b) {
		    less = true;
		}
		
	    }
	}

	
	return less;
	
    }
    
    
    private static List getPathes(ArrayList list) 
    {
		
	List result = new ArrayList();

	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    result.add(term.getLabelledBranches());
	}
		    
	return result;
    }    


    private List getLabelledBranches() {

        List result = new ArrayList();
		
	if (this.isVariable()) {
	    result.add(new ArrayList());
	} else if (this.isConstant()) {
	    result.add(new ArrayList());    
	} else {
	    
	    for (int i=0; i<subterms.length; i++) {
		List list = subterms[i].getLabelledBranches();

		for (int j=0; j<list.size(); j++) {
		    List tmp = (List)list.get(j);
		    tmp.add(new Integer(operation.getPriority()));
	            result.add(tmp);
		}
	    }
	    
	}

	return result;
	
    }
    
    
    private Vector getAssocSubterms(Operation op) throws TermException {

	Vector result = new Vector();
     
	if (!op.isAssociative()) {
	    throw new TermException();
	}

	if (isVariable()) {
	    result.addElement(this);
	} else {
	    Operation o = this.getTopOperation();
	    if (o.equals(op)) {
		Term[] sub = this.getSubterms();
		result = sub[0].getAssocSubterms(op);
		Vector v = sub[1].getAssocSubterms(op);
		for (int i=0; i<v.size(); i++) {
		    Term tmp = (Term)v.elementAt(i);
		    result.addElement(tmp);
		}
	    } else {
		result.addElement(this);
	    }
	}
	return result;
    }


    protected Vector getAssocSubterms(Signature sig, Operation op) 
	throws TermException {

	Vector result = new Vector();
     
	if (!op.isAssociative()) {
	    throw new TermException();
	}

	if (isVariable()) {
	    result.addElement(this);
	} else {
	    Operation o = this.getTopOperation();

	    if (o.equals(op) || o.less(sig,op) || op.less(sig,o)) {
		Term[] sub = this.getSubterms();
		result = sub[0].getAssocSubterms(sig,op);
		Vector v = sub[1].getAssocSubterms(sig,op);
		for (int i=0; i<v.size(); i++) {
		    Term tmp = (Term)v.elementAt(i);
		    result.addElement(tmp);
		}
	    } else {
		result.addElement(this);
	    }
	}
	return result;
    }


    protected boolean isComposite() {
	boolean result = true;

	if (isVariable()) {
	    result = false;
	} else {
	    result = !operation.isConstant();
	}

	return result;
    }


    public Term subst(Signature sig, Variable v, Term t) {

	Term result = null;

	try {
	    if (isVariable()) {
		if (var.equals(v)) {
		    result = t;
		} else {
		    result = new Term(var);
		}
	    } else {
		Term[] tmp = new Term[subterms.length];
		for (int i=0; i<subterms.length; i++) {
		    tmp[i] = subterms[i].subst(sig,v,t);
		}
		result = new Term(sig,operation,tmp);
	    }
	} catch (TermException e) {
	    //System.out.println(e.getMessage());
	    e.printStackTrace();
	}

	return result;
    }



    public Term subst(Variable v, Term t) {

	Term result = null;

	try {
	    if (isVariable()) {
		if (var.equals(v)) {
		    result = t;
		} else {
		    result = new Term(var);
		}
	    } else {
		Term[] tmp = new Term[subterms.length];
		for (int i=0; i<subterms.length; i++) {
		    tmp[i] = subterms[i].subst(v,t);
		}
	
		result = new Term(operation,tmp);
	    }
	} catch (Exception e) {
	}

	return result;
    }



    public boolean isDefinedOn(Signature sig) {
	boolean result = true;

	if (var != null) {
	    result = sig.containsVariable(var);
	} else {
	    result = sig.containsOperation(operation);

	    for (int i=0; i<subterms.length && result; i++) {
		result = subterms[i].isDefinedOn(sig);
	    }

	}

	return result;
    }


    public Term extract(Vector termlist) throws TermException {


	Term result = null;

	if (var != null) {
	    boolean found = false;
	    int index = -1;
	    for (int i =0; i<termlist.size() && !found; i++) {
		Term tmp = (Term)termlist.elementAt(i);
		if (this.equals(tmp)) {
		    found = true;
		    index = i;
		}
	    }

	    ModuleName modName = new ModuleName("TRUTH-VALUE");
	    if (!found) {
		Sort sort = new Sort("Bool", modName);
		Variable var = new Variable("B"+termlist.size(), sort);
		result = new Term(var);
		termlist.addElement(this);
	    } else {
		Sort sort = new Sort("Bool", modName);
		Variable var = new Variable("B"+index, sort);
		result = new Term(var);               
	    }
	    return result;

	}

	Operation op = operation;
	if (op.equals(BoolModule.trueOp)) {
	    result = new Term(op, new Term[0]);
	    return result;
	} else if (op.equals(BoolModule.falseOp)) {
	    result = new Term(op, new Term[0]);
	    return result;
	} else if (op.equals(BoolModule.and) ||
		   op.equals(BoolModule.or) ) {
	    Term[] subs = new Term[subterms.length];;
	    subs[0] = subterms[0].extract(termlist);
	    subs[1] = subterms[1].extract(termlist);
	    result = new Term(op, subs);
	    return result;
	} else if (op.equals(BoolModule.not)) {
	    Term[] subs = new Term[subterms.length];
	    subs[0] = subterms[0].extract(termlist);
	    result = new Term(op, subs);           
	    return result;
	} else {
	    boolean found = false;
	    int index = -1;
	    for (int i =0; i<termlist.size() && !found; i++) {
		Term tmp = (Term)termlist.elementAt(i);
		if (this.equals(tmp)) {
		    found = true;
		    index = i;
		}
	    }

	    ModuleName modName = new ModuleName("TRUTH-VALUE");
	    if (!found) {
		Sort sort = new Sort("Bool", modName);
		Variable var = new Variable("B"+termlist.size(), sort);
		result = new Term(var);
		termlist.addElement(this);
	    } else {
		Sort sort = new Sort("Bool", modName);
		Variable var = new Variable("B"+index, sort);
		result = new Term(var);               
	    }
	    return result;
	}

    }


    public Variable[] getVariables() {

	Variable[] result = new Variable[0];

	if (var != null) {
	    result = new Variable[1];
	    result[0] = var;
	} else {
	    Vector mid = new Vector();
	    for (int i=0; i<subterms.length; i++) {
		Variable[] tmp = subterms[i].getVariables();

		for (int j=0; j<tmp.length; j++) {
		    boolean found = false;
		    for (int k=0; k<mid.size() && !found; k++) {
			Variable vtmp = (Variable)mid.elementAt(k);
			if (vtmp.equals(tmp[j])) {
			    found = true;
			}
		    }
		    if (!found) {
			mid.addElement(tmp[j]);
		    }
		}

	    }

	    result = new Variable[mid.size()];
	    mid.copyInto(result);

	}

	return result;
    }


    public static boolean subsume(Term[] targets, 
				  Term[] samples,
				  Substitution subst) {

	try {
	    if (targets.length != samples.length) {
		return false;
	    }

	    if (targets.length == 0) {
		return true;
	    } else {

		Term tar = targets[0];
		Term sam = samples[0];

		if (sam.var != null) {
		    if (tar.contains(sam.var)) {
			return false;
		    } else {
			subst.addSubst(sam.var, tar);
			Term[] ntargets = new Term[targets.length-1];
			Term[] nsamples = new Term[samples.length-1];

			for (int i=0; i<ntargets.length; i++) {
			    ntargets[i] = targets[i+1].subst(sam.var, tar);
			    nsamples[i] = samples[i+1].subst(sam.var, tar);
			}

			return subsume(ntargets, nsamples, subst);
		    }
		} else {
		    if (tar.operation != null && tar.operation.equals(sam.operation)){
			int arity = tar.operation.getArity();
			int len = targets.length-1+arity;
			Term[] ntargets = new Term[len];
			Term[] nsamples = new Term[len];

			if (tar.operation.getArity() > 0) {
			    System.arraycopy(tar.subterms, 0, ntargets, 0, arity);
			    System.arraycopy(sam.subterms, 0, nsamples, 0, arity);
			}
			System.arraycopy(targets, 1, ntargets, arity, targets.length-1);
			System.arraycopy(samples, 1, nsamples, arity, samples.length-1);

			return subsume(ntargets, nsamples, subst);

		    } else {
			return false;
		    }
		}
	    }
	} catch (SubstitutionException e) {
	    return false;
	}
    }


    public boolean contains(Variable v) {

	boolean result = false;

	if (var != null && var.equals(v)) {
	    result = true;
	} else if (operation != null) {
	    for (int i=0; i<subterms.length && !result; i++) {
		result = subterms[i].contains(v);
	    }
	}

	return result;
    }


    public Substitution subsume(Term term) {

	Substitution subst = new Substitution();

	Term[] targets = new Term[1];
	targets[0] = this;

	Term[] samples = new Term[1];
	samples[0] = term;

	boolean res = subsume(targets, samples, subst);

	if (res) {
	    return subst;
	} else {
	    return null;
	}

    }


  
    public static Substitution unify(Term[] targets, 
				     Term[] samples,
				     Substitution subst) 
	throws NoUnifierException {
 
	if (targets.length != samples.length) {
	    throw new NoUnifierException();
	}

	if (targets.length == 0) {
	    return subst;
	} else {

	    Term tar = targets[0];
	    Term sam = samples[0];

	    if (sam.var != null) {  
		if (tar.contains(sam.var)) {  
		    throw new NoUnifierException();
		} else {
		    try {
			subst.addSubst(sam.var, tar);
		    } catch (SubstitutionException e) {}
		    Term[] ntargets = new Term[targets.length-1];
		    Term[] nsamples = new Term[samples.length-1];

		    for (int i=0; i<ntargets.length; i++) {
			ntargets[i] = targets[i+1].subst(sam.var, tar);	    
			nsamples[i] = samples[i+1].subst(sam.var, tar);
		    }

		    return unify(ntargets, nsamples, subst);
		}
	
	    } else if (tar.var != null) {
	  
		if (sam.contains(tar.var)) {  
		    throw new NoUnifierException();
		} else {
	    
		    try {
			subst.addSubst(tar.var, sam);
		    } catch (SubstitutionException e) {}

		    Term[] ntargets = new Term[targets.length-1];
		    Term[] nsamples = new Term[samples.length-1];

		    for (int i=0; i<ntargets.length; i++) {
			ntargets[i] = targets[i+1].subst(tar.var, sam);
			nsamples[i] = samples[i+1].subst(tar.var, sam);
		    }

		    return unify(ntargets, nsamples, subst);
		}

	  
	    } else {
	  
		if (tar.operation != null &&
		    tar.operation.equals(sam.operation)){
	    	    
		    int arity = tar.operation.getArity();
		    int len = targets.length-1+arity;
		    Term[] ntargets = new Term[len];
		    Term[] nsamples = new Term[len];

		    if (tar.operation.getArity() > 0) {
			System.arraycopy(tar.subterms, 0, ntargets, 0, arity);
			System.arraycopy(sam.subterms, 0, nsamples, 0, arity);
		    }
		    System.arraycopy(targets,
				     1,
				     ntargets,
				     arity,
				     targets.length-1);
		    System.arraycopy(samples,
				     1,
				     nsamples,
				     arity,
				     samples.length-1);
		    return unify(ntargets, nsamples, subst);

		} else {      
		    throw new NoUnifierException(); 
		}
	    }
	}
 
    }



    // unify two arrays of terms wrt the given substitution and signature 
    public static Substitution unify(Term[] targets, 
				     Term[] samples,
				     Substitution subst,
				     Signature sig) 
	throws NoUnifierException {
	
	if (targets.length != samples.length) {
	    throw new NoUnifierException();
	}

	if (targets.length == 0) {
	    return subst;
	} else {

	    Term tar = targets[0];
	    Term sam = samples[0];

	    if (sam.var != null) {  
		if (tar.contains(sam.var)) {  
		    throw new NoUnifierException();
		} else {
		    try {
			subst.addSubst(sam.var, tar, sig);
		    } catch (SubstitutionException e) {}
		    
		    Term[] ntargets = new Term[targets.length-1];
		    Term[] nsamples = new Term[samples.length-1];

		    Hashtable ht = new Hashtable();
		    ht.put(tar.var, sam);
		    
		    for (int i=0; i<ntargets.length; i++) {
			ntargets[i] = targets[i+1].subst(ht, sig);	    
			nsamples[i] = samples[i+1].subst(ht, sig);
		    }

		    return unify(ntargets, nsamples, subst, sig);
		}
	
	    } else if (tar.var != null) {
	  
		if (sam.contains(tar.var)) {  
		    throw new NoUnifierException();
		} else {
	    
		    try {
			subst.addSubst(tar.var, sam, sig);
		    } catch (SubstitutionException e) {
		    }

		    Term[] ntargets = new Term[targets.length-1];
		    Term[] nsamples = new Term[samples.length-1];
		    
		    Hashtable ht = new Hashtable();
		    ht.put(tar.var, sam);
		    
		    for (int i=0; i<ntargets.length; i++) {
			ntargets[i] = targets[i+1].subst(ht, sig);
			nsamples[i] = samples[i+1].subst(ht, sig);
		    }

		    return unify(ntargets, nsamples, subst, sig);
		}

	  
	    } else {
	  
		if (tar.operation != null &&
		    tar.operation.equals(sam.operation)){
	    	    
		    int arity = tar.operation.getArity();
		    int len = targets.length-1+arity;
		    Term[] ntargets = new Term[len];
		    Term[] nsamples = new Term[len];

		    if (tar.operation.getArity() > 0) {
			System.arraycopy(tar.subterms, 0, ntargets, 0, arity);
			System.arraycopy(sam.subterms, 0, nsamples, 0, arity);
		    }
		    System.arraycopy(targets,
				     1,
				     ntargets,
				     arity,
				     targets.length-1);
		    System.arraycopy(samples,
				     1,
				     nsamples,
				     arity,
				     samples.length-1);
		    return unify(ntargets, nsamples, subst, sig);

		} else {      
		    throw new NoUnifierException(); 
		}
	    }
	}
 
    }


    
    // unify two terms wrt the given substitution
    public Substitution unify(Term term, Substitution subst)
	throws NoUnifierException {
	Term[] targets = new Term[] {this};
	Term[] samples = new Term[] {term};
	return unify(targets, samples, new Substitution());
    }

    // unify two arrays of terms wrt the given  substitution and signature
    public Substitution unify(Term term, Substitution subst, Signature sig)
	throws NoUnifierException {
	Term[] targets = new Term[] {this};
	Term[] samples = new Term[] {term};
	return unify(targets, samples, new Substitution(), sig);
    }
    
    // unify this term and an input term
    public Substitution unify(Term term)  throws NoUnifierException {
	return unify(term, new Substitution());
    }

    // unify this term and an input term wrt a signature 
    public Substitution unify(Term term, Signature sig)
	throws NoUnifierException {
	return unify(term, new Substitution(), sig);
    }


    public Term apply(Substitution subst) {

	Term result = this;
	SingleSubstitution[] ss = subst.getAll();
	for (int i=0; i<ss.length; i++) {
	    Variable var = ss[i].getVariable();
	    Term term = ss[i].getTerm();
	    result = result.subst(var, term);
	}

	return result;   

    }


    public boolean  isGround() {

	Variable[] vs = getVariables();

	return (vs.length == 0);

    }


    public boolean contains(Operation op) {

	boolean result = false;

	if (var == null) {
	    if (operation.equals(op)) {
		result = true;
	    } else {
		for (int i=0; i<subterms.length && !result; i++) {
		    result = subterms[i].contains(op);
		}
	    }
	}

	return result;
    }


    /*
    public boolean containsMiddle(Operation op, ArrayList nocrashed) {

	if (var == null) {

	    boolean found = false;
	    for (int i=0; i<nocrashed.size(); i++) {
		Operation opr = (Operation)nocrashed.get(i);
		if (this.operation.equals(opr)) {
		    found = true;
		    break;
		}
	    }


	    if (found) {
		for (int i=0; i<subterms.length; i++) {
		    if (subterms[i].contains(op)) {
			return true;
		    }
		}
	    }
	    
	}

	return false; 	
    }
    */

    public boolean madeBy(Operation[] ops) {

	boolean result = true;

	if (var == null) {
	    boolean found = false;        
	    if (!operation.isBehavorial()) {
		found = true;
	    } else {
		for (int i=0; i<ops.length && !found; i++) {
		    found = operation.equals(ops[i]);
		}
	    }

	    if (!found) {
		result = false;
	    } else {
		for (int i=0; i<subterms.length && result; i++) {
		    result = subterms[i].madeBy(ops);
		}
	    }
	}

	return result;
    }



    public Term getBooleanSubterm() {

	Term result = null;

	if (getSort().getName().equals("Bool")) {
	    result = this;
	} else if (operation != null) {
	    for (int i=0; i<subterms.length; i++) {
		result = subterms[i].getBooleanSubterm();
		if (result != null) break;
	    }
	}
	return result;

    }


    public boolean needRetract() {

	boolean result = false; 

	for (int i=0; i<retract.length; i++) {
	    result = retract[i] != null;
	    if (result)
		return true;
	}
	
	if (subterms != null) {
	    for (int i=0; i<subterms.length; i++) {
		result = subterms[i].needRetract();
		if (result)
		    return true;
	    }
	}

	return result;
    }


    public boolean needExplicitRetract() {

	if (operation != null) {
	    
	    if (operation.info.equals("system-retract")) {
		return true;
	    } else {
		for (int i=0; i<subterms.length; i++) {
		    if (subterms[i].needExplicitRetract())
			return true;
		}
	    }
	}
	
	return false;
    }
    
    public boolean needHeadRetract() {

	boolean result = false; 

	for (int i=0; i<retract.length; i++) {
	    result = retract[i] != null;
	    if (result)
		return true;
	}

	return result;
    }


    
    public Term addAnnotation(String name, Signature sig, Map env) {

	Term term = this;
	if (var != null) {
	    term = new Term(var.addAnnotation(name, env));
	} else {
	    Operation op = operation.addAnnotation(name, env);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].addAnnotation(name, sig, env);
	    }
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.out.println(op);
		System.out.println("--------------------------");
		System.out.println(args[0].showStructure());
		System.out.println("--------------------------");
		System.out.println(args[1].showStructure());
		System.out.println("--------------------------");
		System.out.println(sig.subsorts);
		System.out.println("--------------------------");
		e.printStackTrace();
		System.exit(0);
	    }

	}

	return term;

    }


    public Term removeAnnotation(String name, Signature sig) {
	
	Term term = this;
	if (var != null) {
	    term = new Term(var.removeAnnotation(name));
	} else {
	    Operation op = operation.removeAnnotation(name);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].removeAnnotation(name, sig);
	    }
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.out.println(op);
		System.out.println(args[0].showStructure());
		System.out.println(args[1].showStructure());
		System.out.println(sig.subsorts);
		e.printStackTrace();
		System.exit(0);
	    }

	}

	return term;

    }




    public Term changeSort(Sort olds, Sort news, Signature sig) {
	
	Term term = this;
	if (var != null) {
	    term = new Term(var.changeSort(olds, news));
	} else {
	    Operation op = operation.changeSort(olds, news);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].changeSort(olds, news, sig);
	    }
	    
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		throw new Error();
	    }

	}

	return term;

    }


    public Term changeModuleName(ModuleName olds,
				 ModuleName news,
				 Signature sig)
    {
	Term term = this;
	if (var != null) {
	    term = new Term(var.changeModuleName(olds, news));
	} else {

	    Operation op = operation.changeModuleName(olds, news);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].changeModuleName(olds, news, sig);
	    }
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		e.printStackTrace();
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.exit(0);
	    }

	}

	return term;

    }



    public Term changeAbsoluteModuleName(ModuleName olds,
					 ModuleName news,
					 Signature sig)
    {
	Term term = this;
	if (var != null) {
	    term = new Term(var.changeAbsoluteModuleName(olds, news));
	} else {

	    Operation op = operation.changeAbsoluteModuleName(olds, news);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].changeAbsoluteModuleName(olds,
							       news,
							       sig);
	    }
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		e.printStackTrace();
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.exit(0);
	    }

	}

	return term;

    }




    public Term changeParameterName(String olds,
				    String news,
				    Signature sig)
    {
	Term term = this;
	if (var != null) {
	    term = new Term(var.changeParameterName(olds, news));
	} else {

	    Operation op = operation.changeParameterName(olds, news);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].changeParameterName(olds, news, sig);
	    }
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		e.printStackTrace();
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.exit(0);
	    }

	}

	return term;

    }

    
    
    public Term replaceOperationName(String oldname, 
				     String newname,
				     Signature sig) {
	Term term = this;
	if (var != null) {
	    term = new Term(var);
	} else {

	    Operation op =
		operation.replaceOperationName(oldname, newname);
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].replaceOperationName(oldname,
							   newname,
							   sig);
	    }
	    try {
		term = new Term(sig, op, args);
	    } catch (Exception e){
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.exit(0);
	    }

	}

	return term;

    }



    public Term changeOperation(Operation from, 
				Operation to,
				Signature sig) {

	
	Term term = this;
	
	if (var != null) {
	    term = new Term(var);
	} else {

	    Operation o = operation.copy();
	    if (o.equals(from)) {
		o = to;
	    } 

            if (o.id != null && o.id.equals(from)) {
		o.id = to;
	    }

	    if (o.implicitId != null && o.implicitId.equals(from)) {
		o.implicitId = to;
	    }
	    
	    Term[] args = new Term[subterms.length];
	    for (int i=0; i<subterms.length; i++) {
		args[i] = subterms[i].changeOperation(from, to, sig);
	    }
	    try {
		term = new Term(sig, o, args);
	    } catch (Exception e){
		System.out.println("got a bug. please email klin@cs.ucsd.edu");
		System.exit(0);
	    }

	}

	return term;

    }


    

    public boolean isSubterm(Term term) {

	boolean result = false;

	if (this.equals(term)) {
	    return true;
	} else if (term.operation != null) {
	    for (int i=0; i<term.subterms.length && !result; i++) {
		result = isSubterm(term.subterms[i]);
	    }
	}

	return result;
    }



    protected boolean equalsIgnoreVariableName(Term term, Hashtable varMap) {

	if (var != null) {
	    if (term.var != null) {
		// find mapping from varMap
		Enumeration e = varMap.keys();
		while (e.hasMoreElements()) {
		    Variable v = (Variable)e.nextElement();
		    if (var.equals(v)) {
			v = (Variable)varMap.get(v);
			if (v.equals(term.var)) {
			    return true;
			} else {
			    return false;
			}
		    }
		}
		varMap.put(var, term.var);
		return true;
	    } else {
		return false;
	    }
	} else if (term.var == null && operation.equals(term.operation)) {
	    for (int i=0; i<subterms.length; i++) {
		if (!subterms[i].equalsIgnoreVariableName(term.subterms[i],
							  varMap)){
		    return false;
		}
	    }
	    return true;
	} else {
	    return false;
	}

    }



    public Term subst(Hashtable ht, Signature sig) {
	
	Term result = null;

	/*
	if (ht.isEmpty()) {
	    return this;
	}
	*/

	try {
	    if (var != null) {
		
		Term term = (Term)ht.get(var);
		if (term == null) {
		    Enumeration ve = ht.keys();
		    while (ve.hasMoreElements()) {
			Object obj = ve.nextElement();
			if (obj instanceof Variable) {
			    Variable v = (Variable)obj;
			    if (var.equals(v)) {
				term = (Term)ht.get(v);
				break;
			    }
			} 
		    }
		}

		if (term != null && term.var != null) {
		    //Sort limit = (Sort)term.getPropertyBy("retract");
		    result = new Term(term.var);
		} else if (term != null && term.operation != null) {
		    
		    result = new Term(sig, term.operation, term.subterms);

		    /*
		    Sort limit = (Sort)term.getPropertyBy("retract");
		    if (limit != null) {
			if (this.parent == null) {
			    // add retract: current to limit

			    Sort[] args = new Sort[] { result.sort };
			    Sort res = limit;
			    Operation retOp = new Operation("r:"+
						     result.sort.getName()+
						     ">"+limit.getName()+
						     "(_)", args, res);
			    retOp.info = "system-retract";
		    
			    result = new Term(sig, 
					    retOp, 
					    new Term[] {result});
				
			} 
		    }
		    */
		    
		}

		if (result == null) {
		    result = new Term(var);
		}

	    } else {
		
		Term[] tmp = new Term[subterms.length];
		for (int i=0; i<subterms.length; i++) {
		    tmp[i] = subterms[i].subst(ht, sig);
		}           

		if (sig.explicitRetract &&
		    operation.info.equals("system-retract")) {

		    if (sig.isSubsort(tmp[0].sort, operation.resultSort)) {
			result = tmp[0];
		    } else {
			result = new Term(sig, operation, tmp);
		    }
		    
		} else if (operation.equals(BOBJModule.getSetsortOperation())&&
			   operation.info.equals("system-default")) {
		
		    result = tmp[1];
		    String sortName = tmp[0].operation.name;
		    Sort[] sorts = sig.getSortsByName(sortName);

		    // sorts[0] must be a part of result.sort
		    if (sig.isSubsort(result.sort, sorts[0])) {
			// do nothing
		    } else if (sig.isSubsort(sorts[0], result.sort)) {
			result.sort = sorts[0];
		    } else if (sig.canApply(sorts[0], result.sort) != null) {
			result.sort = sorts[0];
		    } else if (sig.hasCommonSupersort(sorts[0], result.sort)) {
			result.sort = sorts[0];
		    } else {
					    
			throw new Error("Sort casting error when cast "+
					result.sort.getName()+" to "+
					sorts[0].getName());
		    }
		    
		    
		} else {
		    result = getMinimumTerm(sig, operation, tmp);
		    if (result == null) {
			result = new Term(sig, operation, tmp);
		    }
                }
	    }
	} catch (Exception e) {
	    //e.printStackTrace();
	}

	return result;
    }


    protected static Term getMinimumTerm(Signature sig,
					 Operation op,
					 Term[] terms) {
	Term result = null;
	Operation[] ops = sig.getSortedOperationsCompatibleWith(op);
    
	for (int i=0; i<ops.length; i++) {
	    try {
		result = new Term(sig, ops[i], terms);
		if (!result.needRetract()) {  
		    return result;
		} else {
		    result = null;
		}
	    } catch (Exception e) {
	    }
	}
    
	return result;
    }


    public Hashtable getMatch(Term pattern,
				 Signature sig) {
	
	Hashtable result = new Hashtable();

	if (pattern.var != null) {

	    Sort vs = pattern.sort;
	    Sort ts = sort;

	    if (!vs.equals(ts) && !sig.isSubsort(ts, vs)) {
		//System.out.println("my god! "+ts+"  "+vs);
		//System.out.println(this.showStructure());
		//System.out.println(pattern.showStructure());

		if (sig.hasCommonSupersort(ts, vs)) {
		    
		} else {
		    return null;
		}
		
	    }

	    if (var == null) {
		try {
		    Term term = new Term(sig, operation, subterms);
		    result.put(pattern.var, term);
		} catch (Exception e) {}

	    } else {
		Term term = new Term(var);
		try {
		    result.put(pattern.var, term);
		} catch (Exception e) {}
	    }

	} else if (this.operation == null) {

	    return null;
	    
	} else {
	    
	    if (this.operation.equals(pattern.operation)) {
		
		Term[] subpatterns = pattern.subterms;
		for (int i=0; i<subterms.length; i++) {
		    Hashtable tmp = subterms[i].getMatch(subpatterns[i],
							 sig);
		    
		    if (tmp == null) {
			return null;
		    } else {
			Enumeration e = tmp.keys();
			while (e.hasMoreElements()) {
			    Variable var = (Variable)e.nextElement();
			    Term trm1 = (Term)tmp.get(var);

			    Term trm2 = null;
			    Enumeration ee = result.keys();
			    while (ee.hasMoreElements()) {
				Variable vtmp = (Variable)ee.nextElement();
				if (vtmp.equals(var)) {
				    trm2 = (Term)result.get(vtmp);
				    break;
				}
			    }

			    if (trm2 == null) {
				result.put(var, trm1);
			    } else if (!trm1.equals(trm2)) {
				return null;
			    }
			}
		    }
		}

	    }  else {
		result = null;
	    }
	}

	//System.out.println("return match result = "+result+"  "+
	//this+"  "+pattern);
	return result;
    }


    public Variable getVariableWithName(String varname) 
    {
	Variable[] vars = getVariables();
	for (int i=0; i<vars.length; i++) {
	    if (vars[i].name.equals(varname)) {
		return vars[i];
	    }
	}

	return null;
    }

    
    public void cleanFlag() 
    {
       this.nocheck = false;
       this.nogcheck = false;
       this.noscheck = false;

       if (var == null) {
	   for (int i=0; i<subterms.length; i++) {
	       subterms[i].cleanFlag();
	   }
	   
       }
       
    }


    public boolean equals(Term term, HashMap map) {

	boolean result = true;;

	if (this.isVariable() && term.isVariable()) {
	    if (this.getVariable().equals(term.getVariable())) {
		return true;
	    } else {
		
		boolean found = false;
		boolean consistent = false;
		
		Iterator itor = map.keySet().iterator();
		while (itor.hasNext()) {
		    Variable key = (Variable)itor.next();
		    if (key.equals(this.var)) {
			Variable val = (Variable)map.get(key);
			found = true;
			
			if (val.equals(term.var)) {
			    consistent = true;
			}

			break;
		    }
		}

		if (found) {
		    return consistent;
		} else {
		    map.put(this.var, term.var);
		    return true;
		}
	    }
	    
	} else if (!this.isVariable() && !term.isVariable()) {
	    
	    Operation op1 = this.getTopOperation();
	    Operation op2 = term.getTopOperation();
	    if (op1.equals(op2)) {
		if (op1.isAssociative() && !op1.isCommutative()) {
		    try {
			Vector v1 = this.getAssocSubterms(op1);
			Vector v2 = term.getAssocSubterms(op2);

			if (v1.size() == v2.size()) {
			    boolean same = true;
			    for (int i=0; i<v1.size(); i++) {
				Term tm1 = (Term)v1.elementAt(i);
				Term tm2 = (Term)v2.elementAt(i);
				same = same && tm1.equals(tm2);
			    }
			    result = same;
			} else {
			    result = false;
			}
		    } catch (TermException e) {}

		} else if (op1.isAssociative() && op1.isCommutative()) {

		    try {
			Vector v1 = this.getAssocSubterms(op1);
			Vector v2 = term.getAssocSubterms(op2);

			if (v1.size() == v2.size()) {
			    boolean same = true;
			    for (int i=0; i<v1.size(); i++) {
				Term tm1 = (Term)v1.elementAt(i);
				boolean found = false;
				for (int j=0; j<v2.size(); j++) {
				    Term tm2 = (Term)v2.elementAt(j);
				    if (tm1.equals(tm2)) {
					v2.remove(tm2);
					found = true;
					break;
				    }
				}
				if (!found) {
				    same = false;
				    break;
				}
			    }
			    result = same;
			} else {
			    result = false;
			}
		    } catch (TermException e) {}
		    
		} else if (op1.equals(BoolModule.metaEq) ||
			   op1.equals(BoolModule.metaNeq)) {

		    if (Equation.debug) {
			System.out.println("what happen: "+this+"  =?=  "+term);
		    }
		    
		    
		    Term[] tm1 = this.getSubterms();
		    Term[] tm2 = term.getSubterms();

		    HashMap hm = (HashMap)map.clone();
		    if (tm1[0].equals(tm2[0], hm) &&
			tm1[1].equals(tm2[1], hm)) {
			map = hm;
			return true;
		    }
		    
		    hm = (HashMap)map.clone();
		    if (tm1[0].equals(tm2[1], hm) &&
			tm1[1].equals(tm2[0], hm)) {
			map = hm;
			return true;
		    }

		    result = false;
		    		    
		} else {
		    
		    Term[] tm1 = this.getSubterms();
		    Term[] tm2 = term.getSubterms();
		    boolean same = true;
		    for (int i=0; i<tm1.length; i++) {
			same &= tm1[i].equals(tm2[i], map);
		    }
		    result = same;
		}
	    } else {
		result = false;
	    }
	} else {
	    result = false;
	}

        return result;
		
    }
    
}


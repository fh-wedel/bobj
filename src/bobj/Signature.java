package bobj;

import java.util.*;
import java.io.*;
/**
 * a class representing the signature in the first order theory.
 *
 * @author Kai Lin
 * @version %I% %G%
 * 
 */
public class Signature implements Serializable {

    Vector sorts = new Vector();
    Vector vars = new Vector();
    Subsort subsorts = new Subsort();
    Vector operations = new Vector();
    Vector tokens = new Vector();
    Hashtable compatible = new Hashtable();

    // data for parsing optimization
    ArrayList firsts = new ArrayList();
    ArrayList lasts = new ArrayList();

    boolean balancedBrackets = true;
    boolean explicitRetract = true;
        
    // alias for system modules QID, NAT or INT
    HashMap alias = new HashMap();

    int parameters = 0;
    
    public Signature() {
	tokens.addElement("=");
	firsts.add("(");
	lasts.add(")");
    }


    public boolean containsSort(Sort s) {
	return sorts.contains(s);
    }


    public boolean containsSystemSort(Sort s) {
	for (int i=0; i<sorts.size(); i++) {
	    Sort sort = (Sort)sorts.elementAt(i);
	    if (sort.equals(s) && sort.getInfo().equals("system-default")) {
		return true;
	    }
	}
	return false;      
    }


    public boolean containsSystemOperation(Operation op) {
	
	for (int i=0; i<operations.size(); i++) {
	    Operation o = (Operation)operations.elementAt(i);
	    if (op.equals(o) &&
		o.info.equals("system-default")) {
		return true;
	    }
	}
	return false;      
	
    }
    
    
    public boolean containsVariable(Variable v) {
	return vars.contains(v);
    }


    public boolean containsOperation(Operation op) {
	
	for (int i=0; i<operations.size(); i++) {
	    Operation o = (Operation)operations.elementAt(i);
	    
	    if (op.equals(o)) {
		return true;
	    }
	}
	return false;  	
	
	//return operations.contains(op);
    }


    public Variable[] getVariablesOnSort(Sort s) {

	Vector v = new Vector();

	Enumeration e = vars.elements();
	while (e.hasMoreElements()) {
	    Variable tmp = (Variable)e.nextElement();
	    if (tmp.getSort().equals(s)) {
		v.addElement(tmp);
	    }
	}

	Variable[] result = new Variable[v.size()];
	v.copyInto(result);
	return result;
    }


    
    public Variable[] getVariables() {

	Variable[] result = new Variable[vars.size()];
        vars.copyInto(result);
	return result;
    }

    
    public Operation[] getOperations() {

	Operation[] result = new Operation[operations.size()];
	operations.copyInto(result);
	return result;
    }


    public Operation[] getOperationsIn(ModuleName modName) {

	Vector vec = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation tmp = (Operation)operations.elementAt(i);
	    if (tmp.modName.equals(modName)) {
		vec.addElement(tmp);
	    }   
	}

	Operation[] result = new Operation[vec.size()];
	vec.copyInto(result);

	return result;
	
    }


    public Operation getOperation(Operation op) {
	
	for (int i=0; i<operations.size(); i++) {
	    Operation tmp = (Operation)operations.elementAt(i);
	    if (tmp.equals(op))
		return tmp;
	}

	return null;
    }

    
    public Operation[] getBehavorialOperations() {

	Vector v = new Vector();

	for (int i=0; i<operations.size(); i++) {
	    Operation tmp = (Operation)operations.elementAt(i);
	    if (tmp.isBehavorial()) {
		v.addElement(tmp);
	    }
	}

	Operation[] result = new Operation[v.size()];
	v.copyInto(result);
	return result;
    }


    public Operation[] getOperations(Sort[] args, Sort res) 
    {

	Vector tmp = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    	    
	    if (op.getArity() == args.length &&
		this.isSubsort(op.resultSort, res)) {

		boolean same = true;
		for (int j=0; j<args.length; j++) {
		    same = args[j].equals(op.argumentSorts[j]);
		    if (!same) break;
		}

		if (same) {
		    tmp.addElement(op);
		}
		
	    }
	    
	}
	
	Operation[] result = new Operation[tmp.size()];
	tmp.copyInto(result);
	return result;	
    }
    

    public Operation[] getOperationsWithCleanName(String na) {
	
	Vector tmp = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.getCleanName().equals(na)) {
		tmp.addElement(op);
	    }
	}

	Operation[] result = new Operation[tmp.size()];
        tmp.copyInto(result);
	return result;
    }
    

    
    public Operation[] getOperationsWithName(String na) {
	
	Vector tmp = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);

	    if (op.getName().equals(na)) {
		tmp.addElement(op);
	    } else {

		String nname = na;
		Vector prod = op.getTokens();

		boolean samename = true;
		for (int j=0; j<prod.size() && samename; j++) {
		    Object obj = prod.elementAt(j);
		    if (obj instanceof Sort) {

			if (nname.startsWith("_")) {
			    nname = nname.substring(1).trim();
			} else if (nname.equals("") && (j == prod.size()-1)) {
			} else {
			    samename = false;
			}
		    } else {

			String piece = (String)obj;
       
			if (nname.startsWith(piece+" ") ||
			    nname.startsWith(piece+"_")) {
			    nname = nname.substring(piece.length()).trim();
			} else if (j == prod.size()-2 && nname.equals(piece)){
			    nname = nname.substring(piece.length()).trim();
			} else {	  
			    samename = false;
			}
		    }
		}

		if (samename && nname.trim().equals("")) {
		    tmp.addElement(op);   
		}
	    }
	}

	Operation[] result = new Operation[tmp.size()];
        tmp.copyInto(result);
	return result;
    }


    public Operation[] getConstants() {

	Vector res = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.isConstant()) {
		res.addElement(op);
	    }
	}

	Operation[] result = new Operation[res.size()];
	res.copyInto(result);
	return result;

    }


    public Operation[] getConstants(String cname) {

	Vector res = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.isConstant() && op.getName().equals(cname)) {
		res.addElement(op);
	    }
	}

	Operation[] result = new Operation[res.size()];
	res.copyInto(result);
	return result;

    }


    public boolean hasOperation(String opname, Sort[] args, Sort res) 
    {
	opname = Operation.normalize(opname);
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (opname.equals(op.name) &&
		res.equals(op.resultSort) &&
		args.length == op.argumentSorts.length) {

		boolean same = true;
		for (int j=0; j<args.length; j++) {
		    if (!args[j].equals(op.argumentSorts[j])) {
			same = false;
			break;
		    }
		}

		if (same) return true;
		
	    }
	    
	}

	return false;
	
    }


    public boolean hasCompatibleOperation(Operation op) 
    {
	for (int i=0; i<operations.size(); i++) {
	    Operation tmp = (Operation)operations.elementAt(i);
	    
	    boolean compatible = tmp.name.equals(op.name) &&
		tmp.getArity() == op.getArity();
	    
	    if (compatible) {
		compatible = hasCommonSubsort(op.resultSort, tmp.resultSort) ||
		    hasCommonSupersort(op.resultSort, tmp.resultSort);
	    }

	    

	    if (compatible) {
		for (int j=0; j<op.argumentSorts.length; j++) {
		    compatible = hasCommonSubsort(op.argumentSorts[j], 
						  tmp.argumentSorts[j]) ||
			hasCommonSupersort(op.argumentSorts[j], 
					   tmp.argumentSorts[j]);
		    if (!compatible) break;

		}
	    }

	    if (compatible && !tmp.modName.equals(op.modName)) {
		return true;
	    }
	}

	return false;
	
    }

   
    public Subsort getSubsorts() {
	return subsorts;	
    }

  
    public void addSort(Sort sort) {
	if (!containsSort(sort)) {

	    if (parameters > 1 && parameters == sorts.size()) {
		sorts.insertElementAt(sort, 2);
	    } else {
		sorts.addElement(sort);
	    }
	}
    }

    public Sort getSuperSort(Sort s1, Sort s2) {
	Sort result = null;

	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (isSubsort(s1,tmp) && isSubsort(s2,tmp)) {
		if (result == null) {
		    result = tmp;
		} else if (isSubsort(tmp,result)) {
		    result = tmp;
		}
	    }  
	}

	return result;
    }


    public boolean hasCommonSubsort(Sort s1, Sort s2) {
	boolean result = false;

	for (int i=0; i<sorts.size() && !result ; i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    result = isSubsort(tmp, s1) && isSubsort(tmp, s2) ;          
	}

	return result;
    }




    public void addVariable(Variable v)
	throws SignatureException
    {
   
	if (!containsSort(v.getSort())) {
	    throw new SignatureException("Variable "+v.getName()+
					 " has an unknown sort: "+
					  v.getSort().getName());
	}

	vars.addElement(v);

	String name = v.getName().trim();

	// insert the name of this variable into tokens
	if (tokens.indexOf(name) == -1) {
	    boolean found = false;
	    for (int i=0; i<tokens.size() && !found; i++) {
		String st = (String)tokens.elementAt(i);
		if (st.length() < name.length()) {
		    tokens.insertElementAt(name, i);
		    found = true;
		}
	    }

	    if (!found) {
		tokens.addElement(name);
	    }
	}


	firsts.add(name);
	lasts.add(name);
	
    }   


    protected void addTokens(ModuleName modName) {

	if (modName.op == ModuleName.ATOM) {
	    String name = modName.atom;
	    if (tokens.indexOf(name) == -1) {
		boolean found = false;
		for (int i=0; i<tokens.size() && !found; i++) {
		    String st = (String)tokens.elementAt(i);
		    if (st.length() < name.length()) {
			tokens.insertElementAt(name, i);
			found = true;
		    }
		}

		if (!found) {
		    tokens.addElement(name);
		}
	    }      
	}
    }


    public void addOperation(Operation op)  throws SignatureException{

	
	// check if all sorts in this signature
	Sort[] args = op.getArgumentSorts();
	Sort rs = op.getResultSort();

	for (int i=0; i<args.length; i++) {
	    if (!containsSort(args[i])) {
		throw new SignatureException("Unknown sort: "+
					     args[i]);
	    }
	}

	if (!containsSort(rs)) {
	    throw new SignatureException("Unknown sort: "+rs);
	}

	// check if op is already in this signature
	if (!containsOperation(op)) {

	    // check properties
	    if (op.getArity() == 2 ) {
		if (op.isAssociative()) {

		} else {
		    Operation[] ops = getOperationsWithName(op.getName());
		    for (int i=0; i<ops.length; i++) {
			if (op.less(this, ops[i]) && ops[i].isAssociative()) {
			    op.setAssociativity(this);
			    break;
			}
		    }
		}
	    }

	    // end checking

	    operations.addElement(op);

	    //begin of adding compatible

	    Vector pool = new Vector();
	    boolean foundOp = false;
	    for (int i=0; i<operations.size() && !foundOp; i++) {
		Operation tmp = (Operation)operations.elementAt(i);
		if (! tmp.equals(op) &&
		    (tmp.less(this,op) || op.less(this, tmp)) ) {
		    foundOp = true;

		    Enumeration e = compatible.keys();
		    while (e.hasMoreElements()) {
			Operation optmp = (Operation)e.nextElement();
			if (optmp.equals(tmp)) {
			    pool = (Vector)compatible.get(optmp);
			    break;
			}
		    }
		}            
	    }

	    if (foundOp) {
		boolean insert = false;
		for (int j=0; j<pool.size() && !insert; j++) {
		    Operation o = (Operation)pool.elementAt(j);
		    if (op.less(this, o)) {
			pool.insertElementAt(op,j);
			insert = true;
		    }
		}
		if (!insert ) {
		    pool.addElement(op);
		}            

		for (int i=0; i<pool.size(); i++) {
		    Operation o = (Operation)pool.elementAt(i);
		    compatible.put(o, pool);
		}

	    } else {
		pool.addElement(op);
		compatible.put(op, pool);
	    }


	    //end of adding compatible

	    if (op.getArity() == 2 &&
		op.id == null &&
		op.implicitId == null) {

		Operation[] ops = getGreaterCompatible(op);
		for (int i=0; i<ops.length; i++) {
		    Operation id = ops[i].getIdentity();
		    if (id != null) {
     
			if (isSubsort(id.resultSort, op.argumentSorts[0]) ||
			    isSubsort(id.resultSort, op.argumentSorts[1])) {
			    op.implicitId = id;
			}
		    }
		}
	    }

	    if (op.getArity() == 2 && op.id != null) {

		for (int i=0; i<operations.size(); i++) {
		    Operation otmp = (Operation)operations.elementAt(i);
		    if (otmp.less(this, op)) {

			if (otmp.id == null &&
			    otmp.implicitId == null &&
			    (isSubsort(op.id.resultSort,
				       otmp.argumentSorts[0]) ||
			     isSubsort(op.id.resultSort,
				       otmp.argumentSorts[1]))) {

			    otmp.implicitId = op.id;

			}
		    }
		}
	    }
      
	    // insert the tokens of this operation into tokens vector
	    String name = op.getName().trim();
	    StringTokenizer st = new StringTokenizer(name," \n\t_");
	    while (st.hasMoreTokens()) {
		String tmp = st.nextToken().trim();

		if (tokens.indexOf(tmp) == -1) {
		    boolean found = false;
		    for (int i=0; i<tokens.size() && !found; i++) {
			String str = (String)tokens.elementAt(i);
			if (str.length() < tmp.length()) {
			    tokens.insertElementAt(tmp, i);
			    found = true;
			}
		    }

		    if (!found) {
			tokens.addElement(tmp);
		    }
		} 

	    }


	} else {

	    Operation oper = getOperation(op);
	    if (op.isAssociative()) {
		oper.isAssociative = true;
	    } else if (op.isCommutative()) {
		oper.setCommutativity();
	    } else if (op.isIdempotent()) {
		oper.setIdempotence();
	    }
	}

	// check consistence

        // handle firsts and lasts
 	Vector tks = op.getTokens();
        Object obj1 = tks.elementAt(0);
	if (obj1 instanceof String) {
	    String symbol = (String)obj1;
	    symbol = symbol.trim();
		
	    if (!firsts.contains(symbol)) {
		firsts.add(symbol);
	    }
	}

        Object obj2 = tks.elementAt(tks.size()-1);
	if (obj2 instanceof String) {
	    String symbol = (String)obj2;
	    symbol = symbol.trim();
		
	    if (!lasts.contains(symbol)) {
		lasts.add(symbol);
	    }
	}	

	if (balancedBrackets && !op.hasBalancedBrackets()) {
	    balancedBrackets = false;
	}
	
	
    }


    public void addSubsort(Sort parent, Sort child) 
	throws SignatureException {
			
	//check if parent and child are in this signature
	
	if (containsSort(parent)) {
	    if (containsSort(child)) {
		try {
		    subsorts.addSubsort(parent, child);
		} catch (SubsortException e) {
		    throw new SignatureException(e.getMessage()); 
		}
	    } else {
		throw new SignatureException("Unknown sort: "+
					     child.getName());
	    }
	} else {
	    throw new SignatureException("Unknown sort: "+parent.getName()); 
	}

	
    }


    public void addSubsorts(Subsort sub)  throws SignatureException {

	
	Hashtable tab = (Hashtable)sub.subsorts.clone();

	Enumeration e = tab.keys();
	while (e.hasMoreElements()) {
	    Sort p = (Sort)e.nextElement();
	    Vector v = (Vector)tab.get(p);
	    for (int i=0; i<v.size(); i++) {
		Sort c = (Sort)v.elementAt(i);
		addSubsort(p,c);
	    }
	}

    }


    public String toString() {

	String result = "";

	Enumeration e = sorts.elements();
	while (e.hasMoreElements()) {
	    Sort tmp = (Sort)e.nextElement();
	    result += tmp+"\n";
	}

	String stmp = subsorts.toString();
	StringTokenizer st = new StringTokenizer(stmp, "\n");
	while (st.hasMoreTokens()) {
	    result += st.nextToken().trim()+"\n";
	}
       
	e = vars.elements();
	while (e.hasMoreElements()) {
	    Variable tmp = (Variable)e.nextElement();
	    result += tmp+"\n";
	}

	e = operations.elements();
	while (e.hasMoreElements()) {
	    Operation tmp = (Operation)e.nextElement();
	    result += tmp+"\n";
	}


	return result;
    }


    public Sort[] getSorts() {
	Sort[] result = new Sort[sorts.size()];
	sorts.copyInto(result);
	return result;
    }


    public Sort getSort(Sort sort) {
	
	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (tmp.equals(sort)) {
		return tmp;
	    }
	}
	
	return null;
    }


    public Sort getPrincipalSort() 
    {
        Sort first = (Sort)sorts.elementAt(0);
	if (first.equals(BoolModule.boolSort) &&
	    first.getInfo().equals("system-default") &&
	    sorts.size() > 2) {
	    return (Sort)sorts.elementAt(2);
	} else {
	    return first;
	}
    }
    

    public Sort[] getHiddenSorts()
    {

	Vector v = new Vector();

	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (tmp.isHidden()) {
		v.addElement(tmp);
	    }
	}

	Sort[] result = new Sort[v.size()];
        v.copyInto(result);
	return result;

    }


    public Sort[] getInitialSorts()
    {

	Vector v = new Vector();

	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (tmp.isInitial()) {
		v.addElement(tmp);
	    }
	}

	Sort[] result = new Sort[v.size()];
        v.copyInto(result);
	return result;

    }

    

    public Sort[] getHiddenSortsByName(String name) 
    {
	Vector vec = new Vector();

	for (int i=0; i<sorts.size(); i++) {
	    Sort sort = (Sort)sorts.elementAt(i);
	    if (sort.isHidden() && sort.getName().equals(name)) {
		vec.addElement(sort);
	    }
	}

	Sort[] result = new Sort[vec.size()];
        vec.copyInto(result);
	return result;
	
    }
    

    public Sort[] getSortsByName(String name) 
    {
	Vector vec = new Vector();

	for (int i=0; i<sorts.size(); i++) {
	    Sort sort = (Sort)sorts.elementAt(i);
	    if (sort.getName().equals(name)) {
		vec.addElement(sort);
	    }
	}

	Sort[] result = new Sort[vec.size()];
        vec.copyInto(result);
	return result;
	
    }
    
   
    public Sort[] getVisibleSorts() {

	Vector v = new Vector();

	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (!tmp.isHidden() && !tmp.getName().equals("Universal")) {
		v.addElement(tmp);
	    }
	}

	Sort[] result = new Sort[v.size()];
	v.copyInto(result);
	return result;

  }



    public Operation getConstant(String on) {
	Operation op = null;

	boolean found = false;
	Enumeration e = operations.elements();
	while (e.hasMoreElements() && !found) {
	    Operation tmp = (Operation)e.nextElement();
	    if (tmp.getName().equals(on) &&
		tmp.getArgumentSorts().length == 0) {
		op = tmp;
		found = true;
	    }
	}

	return op;
    }


    public Operation getConstant(String on, Sort sort) {

	Enumeration e = operations.elements();
	while (e.hasMoreElements()) {
	    Operation tmp = (Operation)e.nextElement();
	    if (tmp.getName().equals(on) &&
		tmp.getArgumentSorts().length == 0 &&
		tmp.getResultSort().equals(sort)) {
		return tmp;
	    }
	}
      
	return null;
    }



    public Operation[] getOperationsWithPriority(int p) {

	Vector res = new Vector();

	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    int pri = op.getPriority();
	    if (p == pri) {
		res.addElement(op);
	    }
	}

	Operation[] result = new Operation[res.size()];
	res.copyInto(result);
	return result;
    }



    public boolean isSubsort(Sort child, Sort parent) {
	return child.equals(parent) || subsorts.isSubsort(parent,child);
    }


    public boolean less(Sort child, Sort parent) {
	return subsorts.isSubsort(parent,child);
    }

    protected Vector getTokens() {
	return (Vector)tokens.clone();
    }

    
    protected String decomposeToken(String st) {        

	String result = null;

	if (st.trim().equals("")) {
	    return "";
	}

	if (st.startsWith("(") || st.startsWith(")") || st.startsWith(",")) {
	    if (st.length() > 1) {
		String tmp = st.substring(1);
		tmp = decomposeToken(tmp);
		if (tmp == null) {
		    return null;
		} else {
		    return st.substring(0,1)+" "+tmp;
		}
	    } else {
		return st;
	    }
	}

	// decompose by tokens
	boolean found = false;
	String sample = "";
	for (int i=0; i<tokens.size() && !found; i++) {
	    sample = (String)tokens.elementAt(i);
	    if (st.startsWith(sample)) {
		found = true;
	    }
	}
  
	if (found) {
	    
	    String tmp = st.substring(sample.length());
	    tmp = decomposeToken(tmp);
	    
	    if (tmp != null) {
		result = sample+" "+tmp;
	    } 
	} else {

	    try {
		int num = Integer.parseInt(st);
		if ((containsSystemSort(new Sort("Nat",
						 new ModuleName("NAT"))) &&
		     num >= 0) ||
		    (containsSystemSort(new Sort("Int",
						 new ModuleName("INT"))) &&
		     num < 0)) {
		    result = st+" ";
		}
		
	    } catch (Exception e) {}
	}
	
	if (result == null) {

	    // handle module expression here
	    if (st.startsWith(".")) {
		String stmp = st.substring(1);
		String tmp = decomposeToken(stmp);
		if (tmp != null) {
		    result = ". "+tmp;
		} else {
		    result = ". "+stmp;
		}
	    } 
	}
	
	return result;
    }


    public boolean containsToken(String st) {
	return (st.equals("=") || tokens.indexOf(st) != -1);
    }


    public boolean contains(Signature signature) {
	boolean result = true;

	for (int i=0; i<signature.sorts.size(); i++) {
	    Sort sort = (Sort)signature.sorts.elementAt(i);
	    result = this.containsSort(sort);
	    if (!result) return false;
	}

	for (int i=0; i<signature.operations.size(); i++) {
	    Operation op = (Operation)signature.operations.elementAt(i);
	    result = this.containsOperation(op);
	    if (!result) return false;     
	}
	
	result = subsorts.contains(signature.subsorts);

	return result;
    }


    public Sort canApply(Sort s1, Sort s2) {
	return subsorts.canApply(s1, s2);
    }

    public Operation[] getSortedOperationsCompatibleWith(Operation op) {
	Vector pool = (Vector)compatible.get(op);

	if (pool == null) {
	    Enumeration e = compatible.keys();
	    while (e.hasMoreElements()) {
		Operation tmp = (Operation)e.nextElement();	    
		if (op.equals(tmp)) {
		    pool = (Vector)compatible.get(tmp);
		}
	    }
	}
    
	if (pool == null) {
	    pool = new Vector();
	    pool.addElement(op);
	}
	Operation[] result = new Operation[pool.size()];
	pool.copyInto(result);
	return result;
    }


    protected Operation[] getGreaterCompatible(Operation op) {

	Vector pool = (Vector)compatible.get(op);
	if (pool == null) {
	    return new Operation[0];
	} else {
	    pool = (Vector)pool.clone();
	    for (int i=0; i<pool.size(); i++) {
		Operation tmp = (Operation)pool.elementAt(i);
		pool.removeElementAt(0);
		if (tmp.equals(op)) {
		    break;
		}
	    }
	}

	Operation[] result = new Operation[pool.size()];
	pool.copyInto(result);
	return result;
	
    }



    public Signature copy() {

	Signature result = new Signature();

	result.sorts = (Vector)sorts.clone();
	result.vars = (Vector)vars.clone();
	result.subsorts = (Subsort)subsorts.clone();
	result.operations = (Vector)operations.clone();
	result.tokens = (Vector)tokens.clone();
	result.compatible = (Hashtable)compatible.clone();
        result.firsts = (ArrayList)firsts.clone();
	result.lasts = (ArrayList)lasts.clone();
	result.balancedBrackets = balancedBrackets;
        result.explicitRetract = explicitRetract;
		
	return result;
    }


    public Operation[] getAttributes() {
      
	Vector pool = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.isAttribute() && !op.isConstant()) {
		pool.addElement(op);
	    }
	}


	Operation[] result = new Operation[pool.size()];
	pool.copyInto(result);
	return result;
    }


    public Operation[] getMethods() {
	Vector pool = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.isMethod() && !op.isConstant()) {
		pool.addElement(op);
	    }
	}

	Operation[] result = new Operation[pool.size()];
	pool.copyInto(result);
	return result;
    }


    public Operation[] getNonBehavorialOperations() {

	Vector pool = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.isNonBehavorial() && !op.isConstant()) {
		pool.addElement(op);
	    } 
	}

	Operation[] result = new Operation[pool.size()];
	pool.copyInto(result);
	return result;
    }


    public Operation[] getOperationsOnInitial() {

	Vector pool = new Vector();
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    if (op.isDefinedOnInitial()) {
		pool.addElement(op);
	    } 
	}

	Operation[] result = new Operation[pool.size()];
	pool.copyInto(result);
	return result;    

    }


    protected Operation getUniqueOperation(String begin,
					   String end,
					   Sort expect) {
	
	Vector pool = new Vector();
	
	for (int i=0; i<operations.size(); i++) {
	    Operation op = (Operation)operations.elementAt(i);
	    String name = op.getName();
            if (name.startsWith(begin) &&
		name.endsWith(end)     &&
		op.getResultSort().equals(expect)) {
		pool.addElement(op);
	    }
	}
	
        if (pool.size() == 1) {
	    return (Operation)pool.elementAt(0);
	}
	
	return null;    
    	
    }




    public void addQidAlias(Sort sort) 
    {
	List list = (List)alias.get("QID");
	if (list == null) {
	    list = new ArrayList();
	}

	if (!list.contains(sort)) {
	    list.add(sort);
	}

	alias.put("QID", list);
	
    }


    public Sort[] getQidAlias() 
    {
	List list = (List)alias.get("QID");
	if (list != null) {
	    
	    Object[] objs = list.toArray();
	    Sort[] sorts = new Sort[objs.length];
	    for (int i=0; i<objs.length; i++) {
		sorts[i] = (Sort)objs[i];
	    }
	    
	    return sorts;
	} else {
	    return null;
	}
		
    }


    public boolean hasUniqueNameFor(Sort sort) 
    {
	
	int count = 0;
	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (tmp.getName().equals(sort.getName())) {
				
		count++;
		if (count > 1) {
		    return false;
		} 
	    }
	}

	if (count == 1) 
	    return true;
	else
	    return false;
	
    }

    
    protected ArrayList getFirsts() {

	ArrayList result = new ArrayList();

	result.add("(");
	
	for (int k=0; k<operations.size(); k++) {
	    Operation op = (Operation)operations.elementAt(k);

	    Vector tokens = op.getTokens();
	    Object obj = tokens.elementAt(0);

	    if (obj instanceof String) {

		String symbol = (String)obj;
		symbol = symbol.trim();
		
		if (!result.contains(symbol)) {
		    result.add(symbol);
		}
	    } 
	}

	for (int k=0; k<vars.size(); k++) {
	    Variable var = (Variable)vars.elementAt(k);
	    result.add(var.name);
	}
	
	return result;

    }



    protected ArrayList getLasts() {

	ArrayList result = new ArrayList();

	result.add(")");
	
	for (int k=0; k<operations.size(); k++) {
	    Operation op = (Operation)operations.elementAt(k);
	    Vector tokens = op.getTokens();
	    Object obj = tokens.elementAt(tokens.size()-1);
	    
	    if (obj instanceof String) {

		String symbol = (String)obj;
		symbol = symbol.trim();
		
		if (!result.contains(symbol)) {
		    result.add(symbol);
		}
	    } 
	}

	for (int k=0; k<vars.size(); k++) {
	    Variable var = (Variable)vars.elementAt(k);
	    result.add(var.name);
	}
	
	return result;

    }


    public boolean hasCommonSupersort(Sort s1, Sort s2) 
    {
	for (int i=0; i<sorts.size(); i++) {
	    Sort sort = (Sort)sorts.elementAt(i);
	    if (!sort.equals(BoolModule.univSort) &&
		this.isSubsort(s1, sort) &&
		this.isSubsort(s2, sort)) {
				
		return true;
	    }
	}
	
	return false;
    }
    

    public Sort[] getDirectSupersorts(Sort sort) 
    {
	ArrayList list = new ArrayList();
	for (int i=0; i<sorts.size(); i++) {
	    Sort tmp = (Sort)sorts.elementAt(i);
	    if (!tmp.equals(BoolModule.univSort) &&
		!tmp.equals(sort) &&
		isSubsort(sort, tmp)) {
		// tmp is candidate, but make sure tmp is not a supersort
		// of a sort in list

		ArrayList buf = new ArrayList();
		boolean add = true;
		for (int j=0; j<list.size(); j++) {
		    Sort s = (Sort)list.get(j);
		    if (isSubsort(s, tmp)) {
			buf.add(s);
			add = false;
		    } else if (isSubsort(tmp, s)) {
			
		    }
		}

		if (add) {
		    buf.add(tmp);
		}
		list = buf;
	    }
	    
	}
		
	Sort[] result = new Sort[list.size()];
	for (int i=0; i<result.length; i++) {
	    result[i] = (Sort)list.get(i);
	}

	return result;
	
    }
  

    public Sort[] getDirectSubsorts(Sort sort) 
    {
	ArrayList list = new ArrayList();
	Vector vec = (Vector)subsorts.subsorts.get(sort);
	if (vec != null) {
	    for (int i=0; i<vec.size(); i++) {
		Sort tmp = (Sort)vec.elementAt(i);
		
		ArrayList buf = new ArrayList();
		boolean add = true;
		for (int j=0; j<list.size(); j++) {
		    Sort s = (Sort)list.get(j);
		    if (isSubsort(s, tmp)) {

		    } else if (isSubsort(tmp, s)) {
			buf.add(s);
			add = false;			
		    }
		}

		if (add) {
		    buf.add(tmp);
		}
		list = buf;		

	    }
	}
		
	Sort[] result = new Sort[list.size()];
	for (int i=0; i<result.length; i++) {
	    result[i] = (Sort)list.get(i);
	}

	return result;
	
    }


  
}












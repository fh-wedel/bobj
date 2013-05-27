
package bobj;

import java.util.*;
import java.io.*;
/**
 *
 * a class representing the operation in the first order signature.
 *
 * @author  Kai Lin
 * @version %I% %G%
 * @see Sort
 * @see Variable
 * @see Signature
 */
public class Operation  implements Serializable {

    String name;
    ModuleName modName;
    Sort[] argumentSorts;
    String[] argumentNames;
    Sort resultSort;
    String resultName;

    int priority;
    boolean isAssociative;
    boolean isCommutative;
    boolean isIdempotent;
    Operation id;
    Operation implicitId;
    boolean behavorial;
    String[] gather;
    int[] strategy;
        
    String info;
    Vector prod;

    static boolean debug = false;

    
    /**
     * create an operaion by the specified name and the sorts of arguments
     * and the sort of result.
     *
     * @param na  the string of the name of this operation, where "_" is
     *            used as the declaration of argument position
     * @param args the sort array of arguments
     * @param res  the sort of result
     * @return an operaion with the specified name and the sorts of
     *          arguments  and the sort of result. Its priority is minimum,
     *           has no defined properties and information.
     * @exception SignatureException
     *     if na is in mix notation and has different arguments as args,
     *        or na is empty string.
     */             
    public Operation(String name, Sort[] args, Sort res, ModuleName modName)
	throws SignatureException {

	if (name.trim().equals("")) {
	    throw new SignatureException("Empty string can't be"+
					 " operation name");
	}

	//inputname = na.trim();
	this.name = normalize(name.trim());
	this.modName = modName;
	this.info = "";
	this.argumentSorts = args;
	this.resultSort = res;

	//check the consistence of arguments.
	if (name.indexOf("_") != -1) {
	    int count = 0;
	    String s = name;
	    int k = s.indexOf("_");
	    while (k != -1) {
		count ++;
		s = s.substring(k+1);
		k = s.indexOf("_");
	    }      
	    if (count != args.length) {
		throw new SignatureException("Expect "+count+
					     " argument(s) for operation "+
					     name);
	    }
	}


	//set priority.
	//priority = new Integer(Integer.MAX_VALUE).intValue();
	
        if (name.trim().indexOf("_") == -1) {
	    priority = 0;
	} else if (!name.trim().startsWith("_") &&
	           !name.trim().endsWith("_")) {
	    priority = 0;
	} else if (!name.trim().startsWith("_") &&
		   name.trim().endsWith("_") &&
		   argumentSorts.length == 1) {
	    priority = 15;
	} else {
	    priority = 41;
	}
	
	
	//set properties.
	isAssociative = false;
	isCommutative = false;
	isIdempotent = false;
	behavorial = true;

	//set information
	info = "";

	//set prod
	prod = new Vector();
	if (args.length ==0) {
	    StringTokenizer ster = new StringTokenizer(name," ");
	    while (ster.hasMoreTokens()) {
		prod.addElement(ster.nextToken());
	    }

	} else if (name.indexOf("_") != -1) {
	    String stmp = name;
	    int index = stmp.indexOf("_");
	    int count = 0;
	    while (index != -1) {
		String st = stmp.substring(0,index).trim();
		if (!st.equals("")) {
		    //prod.addElement(st);
		    StringTokenizer ster = new StringTokenizer(st," ");
		    while (ster.hasMoreTokens()) {
			prod.addElement(ster.nextToken());
		    }             
		}
		prod.addElement(args[count]);
		count ++;
		stmp = stmp.substring(index+1);
		index = stmp.indexOf("_");
	    }
	    if (!stmp.equals("")) {
		StringTokenizer ster = new StringTokenizer(stmp," ");
		while (ster.hasMoreTokens()) {
		    prod.addElement(ster.nextToken());
		}
	    }
	} else {
	    prod.addElement(name);
	    prod.addElement("(");
	    for (int i=0; i<args.length; i++) {
		prod.addElement(args[i]);
		if (i<args.length-1) {
		    prod.addElement(",");
		}
	    }
	    prod.addElement(")");
	}
    }


    public Operation(String name, Sort[] args, Sort res)
	throws SignatureException {
	this(name, args, res, null);
    }

    
    public Operation(String name, Sort res)
	throws SignatureException {
	this(name, new Sort[0], res, null);
    }

    
    public ModuleName getModuleName() 
    {
	return modName;
    }
    
    
    protected static String normalize(String name) {

	String result = "";

	String tmp = name;
	int i = tmp.indexOf("_");
	while ( i != -1) {
	    if (result.endsWith("_")) {
		result += " "+tmp.substring(0, i).trim();
	    } else {
		result += tmp.substring(0, i).trim();
	    }
	    if (!result.endsWith("_") && !result.endsWith(" ")) {
		result += " _";
	    } else {
		result += "_";
	    }
	    tmp = tmp.substring(i+1).trim();
	    i = tmp.indexOf("_");
	}

	if (result.endsWith("_")) {
	    result += " "+tmp.trim();
	} else {
	    result += tmp.trim();
	}

	return result.trim();
    }


    /*
     * create a constant with the specified name and sort.
     *
     * @param na  the string of the name of this operation, which 
     *              doesn't contain "_" .
     * @param res  the sort of result .
     * @exception SignatureException
     *      if na contains "_"  or na is empty string.
     */
    public Operation(String name,  Sort res,  ModuleName modName) 
	throws SignatureException 
    {
	this(name, new Sort[0], res, modName);
    }


    /**
     * set associativity for this operation.
     *
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setAssociativity() throws SignatureException {
	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];
	    if (firstSort.equals(resultSort) && secondSort.equals(resultSort)) {
		isAssociative = true;
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "associativity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}
      
    }


    /**
     * set associativity for this operation.
     *
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setAssociativity(Signature sig) throws SignatureException {

	if (argumentSorts.length == 2) {

	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];

	    boolean lcanset =  sig.isSubsort(resultSort, firstSort) ||
		sig.isSubsort(firstSort, resultSort) ;

	    if (!lcanset) {
		lcanset = sig.hasCommonSubsort(resultSort,firstSort);
	    }

	    boolean rcanset =  sig.isSubsort(resultSort, secondSort) ||
		sig.isSubsort(secondSort, resultSort) ;

	    if (!rcanset) {
		rcanset = sig.hasCommonSubsort(resultSort,secondSort);
	    }


	    if (lcanset && rcanset) {
		isAssociative = true;
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "associativity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}
      
    }





    /**
     * set communtativity for this operation.
     *
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setCommutativity() throws SignatureException{
	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];
	    if (firstSort.equals(secondSort)) {
		isCommutative = true;
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "communtativity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}    
    }




    /**
     * set communtativity for this operation.
     *
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setCommutativity(Signature sig) throws SignatureException{
	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];

	    boolean canset = sig.getSuperSort(firstSort, secondSort) != null;

	    if (canset) {
		isCommutative = true;
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "communtativity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}    
    }





    /**
     * set idempotence for this operation.
     *
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setIdempotence() throws SignatureException{
	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];
	    if (firstSort.equals(secondSort)) {
		isIdempotent = true;
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "idempotence");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}    
    }


    /**
     * set identity for this operation.
     *
     * @param op a constant which is the identity of this opertaion.
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setIdentity(Operation op)  throws SignatureException {

	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];
	    Sort resultSort = op.getResultSort();

	    if (resultSort.equals(firstSort) && resultSort.equals(secondSort)) {
		if (op.argumentSorts.length == 0 ) {
		    id = op;
		} else {
		    throw new SignatureException("Inconsistent argument sorts for "+
						 "identity");
		}
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "identity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}    
    }



    public void setIdentity(Signature sig, Operation op)
	throws SignatureException {

	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];

	    if (sig.isSubsort(op.resultSort, firstSort) || 
		sig.isSubsort(op.resultSort, secondSort)) {
		if (op.argumentSorts.length == 0 ) {
		    id = op;
		} else {
		    throw new SignatureException("Inconsistent argument sorts for "+
						 "identity");
		}
	    } else {
		throw new SignatureException("Inconsistent argument sorts for "+
					     "identity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}    
    }



    /**
     * set identity for this operation.
     *
     * @param op a constant which is the identity of this opertaion.
     * @exception SignatureException
     *            if this operation is not binary operation
     *            or has not consistent arguments sort.
     */

    public void setIdentity(Operation op, Signature sig)
	throws SignatureException {

	if (argumentSorts.length == 2) {
	    Sort firstSort = argumentSorts[0];
	    Sort secondSort = argumentSorts[1];
	    Sort resultSort = op.getResultSort();

	    if (sig.isSubsort(resultSort, firstSort) ||
		sig.isSubsort(resultSort,secondSort)) {
		if (op.argumentSorts.length == 0 ) {
		    id = op;

		} else {
		    throw new SignatureException("Inconsistent argument"+
						 " sorts for identity");
		}
	    } else {
		throw new SignatureException("Inconsistent argument sorts "+
					     "for identity");
	    }      
	} else {
	    throw new SignatureException("Expect two arguments for "+name);
	}    
    }





    /**
     * set information as the specified string.
     *
     * @param s string
     */
    public void setInfo(String s) {
	info = s ;
    }



    /**
     * return a string representing this operation.
     * Example:  <P>op if_then_else : Bool Nat Nat -> Nat [prec 100] .
     *
     */
    public String toString() {
	String result = "op ";

	result += name + " :";

	for (int i=0; i<argumentSorts.length; i++) {
	    Sort tmp = argumentSorts[i];
	    result += " "+tmp.getName()+"."+tmp.getModuleName();
	}

	result += " -> "+resultSort.getName()+"."+
	    resultSort.getModuleName()+"  ";
	result += "[";

	if (isAssociative) result += " assoc";
	if (isCommutative) result += " comm";
	if (isIdempotent) result += " idem";
	if (id != null) result += " idr: "+id.getName();
	if (!behavorial) result += "ncong";
		
	if (priority != new Integer(Integer.MAX_VALUE).intValue()) {
	    result += " prec "+priority;
	}

	if (gather != null) {
	    result += " gather(";
	    for (int i=0; i<gather.length; i++) {
		if (i != 0) {
		    result += ", ";
		}
		result += gather[i];
	    }
	    result += ")";
	}

        if (strategy != null) {
	    result += " strategy(";
	    for (int i=0; i<strategy.length; i++) {
		if (i != 0) {
		    result += ", ";
		}
		result += strategy[i];
	    }
	    result += ")";	
	}
			    
	if (result.endsWith("[")) {
	    result = result.substring(0, result.length()-1);
	} else {
	    result += " ] ";
	}	
	
	//result += modName;
		
	return result;
    }




    /**
     * return the name of this operation.
     */
    public String getName() {
	return name;
    }


    public String getCleanName() {
	String result = name.trim();
	if (result.startsWith("_")) {
	    result = result.substring(1).trim();
	}

	if (result.endsWith("_")) {
	    result = result.substring(0,result.length()-1).trim();
	}

	if (result.indexOf("_") != -1) {
	    result = name;
	}

	return result;

    }


    /**
     * return the vector of the argument sorts. This vector can be modified
     * without any side effect.
     */
    public Sort[] getArgumentSorts() {
	return argumentSorts;
    }


    /**
     * return the i_th argument sort.
     *
     * @exception SignatureException
     *         if i is less then 0 or greater than the number of arguments.
     */
    public Sort getArgumentSortAt(int i) throws SignatureException {
	Sort result = null;
	if (i<argumentSorts.length) {
	    result = argumentSorts[i];
	} else {
	    throw new SignatureException(
					 "The number of arguments out of bound "+i);
	}
	return result;
    }


    /**
     * return the result sort.
     *
     */
    public Sort getResultSort() {
	return resultSort;
    }


    /**
     * return the priority of this operation.
     *
     */
    public int getPriority() {
	return priority;
    }


    /**
     * return the arity of this operation.
     */
    public int getArity() {
	return argumentSorts.length;
    }


    /**
     * return the information of this operation.
     *
     */
    public String getInfo() {
	return info;
    }


    /**
     * return the identity of this operation.
     *
     */
    public Operation getIdentity() {
	if (id != null) {
	    return id;
	} else if (implicitId != null) {
	    return implicitId;
	} else {
	    return null;
	}
    }


    /**
     *
     * test if this operation is a constant.
     *
     */
    public boolean isConstant() {
	return argumentSorts.length==0;
    }

    /**
     *
     * test if this operation is associative.
     *
     */
    public boolean isAssociative() {
	return isAssociative;
    }

    /**
     *
     * test if this operation is commutative.
     *
     */
    public boolean isCommutative() {
	return isCommutative;
    }

    /**
     *
     * test if this operation is idempotent.
     *
     */
    public boolean isIdempotent() {
	return isIdempotent;
    }

    /**
     *
     * test if this operation is in mix notation.
     *
     */
    public boolean isMixNotation() {
	return name.indexOf("_") != -1;
    }

    /** 
     *
     * test if this operation is equal to the specified operation.
     *
     * @param op operation
     * @return true if this operation is equals to op.
     */

    public boolean equals(Object obj) {

	
	if (obj instanceof Operation) {
		    
	    Operation op = (Operation)obj;
       	    if (name.equals(op.name) &&
	        resultSort.equals(op.resultSort) &&
		argumentSorts.length == op.argumentSorts.length ) {
				
		for (int i=0; i<argumentSorts.length; i++) {
		    if (!argumentSorts[i].equals(op.argumentSorts[i])) {
			return false;
		    }
		}

		if (modName != null && op.modName != null) {
		    return modName.equals(op.modName);
                } else if (modName == null && op.modName == null) {
		    return true;
		}
		
	    } 
	    
	}
		
	
	return false;
    }



    public boolean hasSameSignature(Operation op) {

	if (resultSort.equals(op.resultSort) &&
	    argumentSorts.length == op.argumentSorts.length ) {

	    for (int i=0; i<argumentSorts.length; i++) {
		if (!argumentSorts[i].equals(op.argumentSorts[i])) {
		    return false;
		}
	    }

	    return true;
	    
	} 	    

	return false;
    }



    
    /*
     * set the priority of this operation .
     *
     * @param pri an positive integer 
     *
     */
    public void setPriority(int pri) {
	if (pri > 0) {
	    priority = pri;
	} else {
	    pri = Integer.MAX_VALUE;
	}
    }


    protected Vector getTokens() {
	return (Vector)prod.clone();
    }


    public void setBehavorial(boolean flag) {
	behavorial = flag;
    }

    public boolean isBehavorial() {
	return behavorial;
    }


    /*
     * check whether this operation is less than another operation op
     * under the specified signature.
     */
    public boolean less(Signature sig, Operation op) {
		
	boolean result = false;
	boolean samename = true;
	if (prod.size() == op.prod.size()) {
	    	    
	    for (int i=0; i<prod.size() && samename; i++) {
		Object obj1 = prod.elementAt(i);
		Object obj2 = op.prod.elementAt(i);
				
		if (obj1 instanceof String) {
		    if (obj2 instanceof String) {

			samename =
			  ((String)obj1).trim().equals(((String)obj2).trim());
			
		    } else {
			samename = false;
		    }
		}

		if (obj1 instanceof Sort) {
		    if (obj2 instanceof Sort) {
			samename = true;
		    } else {
			samename = false;
		    }
		} 
	    }

	} else if (op.getArity() == 1 && getArity() == 1) {
	    samename = name.trim().equals(op.name.trim()+" _") ||
		op.name.trim().startsWith(name.trim()+" _");
	} else {
	    samename = false;
	}
		
	if (samename && this.getArity() == op.getArity()) {

	    if (getArity() != 0) {
		boolean less = false;
		boolean comparable = true;

		for (int i=0; i<argumentSorts.length && comparable; i++) {
		    Sort s1 = (Sort) argumentSorts[i];
		    Sort s2 = (Sort) op.argumentSorts[i];
		   		   
		    if (sig.isSubsort(s1,s2)) {
			less = less || sig.less(s1, s2);		 
		    } else {
			comparable = false;
		    }
		}
		
		if (comparable && less) {    
		    result = sig.isSubsort(resultSort, op.resultSort);
		} else if (comparable) {
		    //result = sig.isSubsort(resultSort, op.resultSort);
		    result = sig.less(resultSort, op.resultSort);
		}

						
	    } else {
		//result = sig.isSubsort(resultSort, op.resultSort);
		if (sig.less(resultSort, op.resultSort)) {
		    result = true;
		}

		/*
		else if (resultSort.equals(op.resultSort)) {
		    if (modName != null &&
			op.modName != null &&
			modName.equals(op.modName)) {
			result = true;
		    } else if (modName == null &&
			       op.modName == null) {
			result = true;
		    }
		}
		*/
	    }
	} 

	return result;
    }


    public boolean isAttribute() {
	return !resultSort.isHidden() &&  behavorial;
    }


    public boolean isMethod() {
	return resultSort.isHidden() &&  behavorial;
    }

    public boolean isNonBehavorial() {
	if (! behavorial) {
	    for (int i=0; i<argumentSorts.length; i++) {
		if (argumentSorts[i].isHidden()) {
		    return true;
		}
	    }
	    if (resultSort.isHidden()) {
		return true;
	    }
	} 
	return false;
    }


    public Operation changeModuleName(ModuleName olds, ModuleName news) {

        Operation result = null;
        Sort[] args = new Sort[argumentSorts.length];
        Sort res = resultSort.changeModuleName(olds, news);

        for (int j=0; j<argumentSorts.length; j++) {
	    args[j] = argumentSorts[j].changeModuleName(olds, news);
        }

	try {

	    if (modName.equals(olds)) {
		result = new Operation(name, args, res, news);
	    } else {
		result = new Operation(name,
				       args,
				       res,
				       modName.changeModuleName(olds, news));
	    }
	    
	    result.priority = priority;
	    result.info = info;
	    result.isAssociative = isAssociative;
	    result.isCommutative = isCommutative;
	    result.isIdempotent =  isIdempotent;

	    if (id != null) {
		result.id = id.changeModuleName(olds, news);
	    }

	    if (implicitId != null) {
		result.implicitId = implicitId.changeModuleName(olds, news);
	    }
	    
	    result.behavorial = behavorial;
	    result.gather = gather;
	    result.strategy = strategy;
	    
	} catch (SignatureException e) {	    
	}
	

	return result;
    }



    public Operation changeAbsoluteModuleName(ModuleName olds,
					      ModuleName news) {
		
        Operation result = null;
        Sort[] args = new Sort[argumentSorts.length];
        Sort res = resultSort.changeAbsoluteModuleName(olds, news);

        for (int j=0; j<argumentSorts.length; j++) {
	    args[j] = argumentSorts[j].changeAbsoluteModuleName(olds, news);
        }

	try {

	    if (modName.equals(olds)) {
		result = new Operation(name, args, res, news);
	    } else {
		result = new Operation(name, args, res, modName);
	    }
	    result.priority = priority;
	    result.info = info;
	    result.isAssociative = isAssociative;
	    result.isCommutative = isCommutative;
	    result.isIdempotent =  isIdempotent;

	    if (id != null) {
		result.id = id.changeAbsoluteModuleName(olds, news);
	    }

	    if (implicitId != null) {
		result.implicitId = implicitId.changeAbsoluteModuleName(olds,
									news);
	    }
	    
	    result.behavorial = behavorial;
	    result.gather = gather;
	    result.strategy = strategy;
	    
	} catch (SignatureException e) {	    
	}
	

	return result;
    }


    public Operation changeParameterName(String olds, String news) {
	
        Operation result = null;
        Sort[] args = new Sort[argumentSorts.length];
        Sort res = resultSort.changeParameterName(olds, news);

        for (int j=0; j<argumentSorts.length; j++) {
	    args[j] = argumentSorts[j].changeParameterName(olds, news);
        }

	try {
	    
	    result = new Operation(name,
				   args,
				   res,
				   modName.changeParameterName(olds,
							       news));
	   	    
	    result.priority = priority;
	    result.info = info;
	    result.isAssociative = isAssociative;
	    result.isCommutative = isCommutative;
	    result.isIdempotent =  isIdempotent;

	    if (id != null) {
		result.id = id.changeParameterName(olds, news);
	    }

	    if (implicitId != null) {
		result.implicitId = implicitId.changeParameterName(olds, news);
	    }
	    
	    result.behavorial = behavorial;
	    result.gather = gather;
	    result.strategy = strategy;
	    
	} catch (SignatureException e) {	    
	}
	

	return result;
    }

    
    
    public Operation addAnnotation(String name, Map env) {

	if (info.equals("system-default")) {
	    return this;
	}

	Integer aInt = (Integer)env.get(modName);
	if (aInt != null && aInt.intValue() == 0) {
	    return this;
	}

	if (modName.hasNotation()) {
	    return this;
	}
		
        Operation result = null;
        Sort[] args = new Sort[argumentSorts.length];
        Sort res = resultSort.addAnnotation(name, env);

        for (int j=0; j<argumentSorts.length; j++) {
	    args[j] = argumentSorts[j].addAnnotation(name, env);
        }

	try {
	    
	    result = new Operation(this.name,
				   args,
				   res,
				   modName.addAnnotation(name));
	    result.priority = priority;
	    result.info = info;
	    result.isAssociative = isAssociative;
	    result.isCommutative = isCommutative ;
	    result.isIdempotent =  isIdempotent ;
	    result.id = id;
	    result.behavorial = behavorial;
	    result.gather = gather;
	    result.strategy = strategy;
	    
	} catch (SignatureException e) {
	} catch (Exception e) {
	    System.out.println(this);
	    System.exit(0);
	}
	

	return result;
    }


    public Operation removeAnnotation(String name) {

        Operation result = null;
        Sort[] args = new Sort[argumentSorts.length];
        Sort res = resultSort.removeAnnotation(name);

        for (int j=0; j<argumentSorts.length; j++) {
	    args[j] = argumentSorts[j].removeAnnotation(name);
        }

	try {

	    result = new Operation(this.name,
				   args,
				   res,
				   modName.getOriginModuleName());
	    result.priority = priority;
	    result.info = info;
	    result.isAssociative = isAssociative;
	    result.isCommutative = isCommutative ;
	    result.isIdempotent =  isIdempotent ;
	    result.id = id;
	    result.behavorial = behavorial;
	    result.gather = gather;
	    result.strategy = strategy;
	    
	} catch (SignatureException e) {
	}

	return result;
    }


    public Operation changeSort(Sort olds, Sort news) {
   
        Operation result = null;
        Sort[] args = new Sort[argumentSorts.length];
        Sort res = resultSort.equals(olds) ? news: resultSort ;

        for (int j=0; j<argumentSorts.length; j++) {
	    args[j] = argumentSorts[j].equals(olds) ? news: argumentSorts[j];
        }

	try {
	    result = new Operation(name, args, res, modName);
	    result.priority = priority;
	    result.info = info;
	    result.isAssociative = isAssociative;
	    result.isCommutative = isCommutative ;
	    result.isIdempotent =  isIdempotent ;
	    if (id != null) 
		result.id = id.changeSort(olds, news);
	    if (implicitId != null)
		result.implicitId = implicitId.changeSort(olds, news);
	    result.behavorial = behavorial;
	    result.gather = gather;
	    result.strategy = strategy;
	    
	} catch (SignatureException e) {
	}

	return result;
    }



    public Operation replaceOperationName(String to) {    
	return this.replaceOperationName(name, to);
    }
    

    public Operation replaceOperationName(String from, String to) {

	Operation result = this;

        boolean same = true;
        StringTokenizer st1 = new StringTokenizer(from, "_ ");
        StringTokenizer st2 = new StringTokenizer(name, "_ ");
        while (st1.hasMoreTokens() && same) {
	    String tmp1 = st1.nextToken();
	    if (st2.hasMoreTokens()) {
		String tmp2 = st2.nextToken();
		if (!tmp1.equals(tmp2)) {
		    same = false;
		    break;
		}
	    } else {
		same = false;
		break;
	    }
        }

        if (st2.hasMoreTokens()) {
	    same = false;
        }

        if (same) {

	    try {
		result = new Operation(to,
				       argumentSorts,
				       resultSort,
				       modName);

		result.isAssociative = isAssociative;
		result.isCommutative = isCommutative;
                result.isIdempotent = isIdempotent;
		result.behavorial = behavorial;

		if (id != null) {
		    result.id = id.replaceOperationName(from, to);
		}

		if (implicitId != null) {
		    result.implicitId = implicitId;
		}

		result.gather = gather;
		result.strategy = strategy;
				
	    } catch (SignatureException e) {
	    }

        } 
	
        return result;

    }


    public boolean uses(Sort sort) {
	for (int i=0; i<argumentSorts.length; i++) {
	    if (argumentSorts[i].equals(sort)) {
		return true;
	    }
	}

	if (resultSort.equals(sort)) {
	    return true;
	}

	return false;

    }


    public boolean isDefinedOnInitial() {
	boolean result = true;
	for (int i=0; i<argumentSorts.length && result; i++) {
	    result = argumentSorts[i].isInitial();
	}

	if (result) result = resultSort.isInitial();
	return result;
    }



    public Operation copy() {
       
	Operation result = null;
       
	try {
	    result = new Operation(name, argumentSorts, resultSort, modName);
	} catch (Exception e){}
       
	result.argumentNames = argumentNames;
	result.resultName = resultName;
	result.priority = priority;
	result.isAssociative = isAssociative;
	result.isCommutative = isCommutative;
	result.isIdempotent = isIdempotent;
	result.id = id ;
	result.implicitId = implicitId;
	result.behavorial = behavorial;
	result.gather = gather;
	result.strategy = strategy;
	
	result.info = info;
	result.prod = (Vector)prod.clone();

	return result;
       
    }


    public void setGather(String[] gather)
	throws SignatureException
    {
	if (gather.length != this.argumentSorts.length) {
	    throw new SignatureException("expect "+argumentSorts.length+
					 " in gather definition");
	}

	this.gather = gather;
       
    }


    public void setStrategy(int[] strategy)
    {
	this.strategy = strategy;       
    }
    

    protected boolean hasBalancedBrackets()
    {

	Stack stack = new Stack();
	
	Vector tokens = getTokens();
	for (int i=0; i<tokens.size(); i++) {
	    Object obj = tokens.elementAt(i);
	    if (obj instanceof String) {
		String str = (String)obj;
		if (str.equals("(") || str.equals("{") || str.equals("[")) {
		    stack.push(str);
		    continue;
		}

		if (str.equals(")") || str.equals("}") || str.equals("]")) {
		    if (stack.isEmpty()) {
			return false;
		    } else {
			String top = (String)stack.pop();
			if ( (top.equals("(") && str.equals(")")) ||
			     (top.equals("[") && str.equals("]")) ||
			     (top.equals("{") && str.equals("}")) ) {
			} else {
			    return false;
			}
		    }
		}
	    }
	}

	if (!stack.isEmpty()) {
	    return false;
	}
		
	return true;
	
    }
    
}




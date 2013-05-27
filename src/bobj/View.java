package bobj;

import java.util.*;

public class View {

    boolean morphism = false;
    String name;
    Module main, source, target, smodule, tmodule;
    Map sortMap, opMap, varMap, trans;
    boolean allowSortDef = true;
    ArrayList views = new ArrayList();
    HashMap record = new HashMap();
    boolean debug = false;


    public void setAsMorphism() {
	morphism = true;
    }
    
    public void record() {
	record.putAll(sortMap);
	record.putAll(opMap);
	record.putAll(varMap);
	record.putAll(trans);
    }
    
    public View copy(String newName) {
	
	View result = new View(newName, source, target);
	result.main = this.main;
	result.smodule = this.smodule;
	result.smodule = this.smodule;
	result.sortMap = this.sortMap;
	result.opMap = this.opMap;
	result.varMap = this.varMap;
	result.trans = this.trans;
	result.allowSortDef = this.allowSortDef;
        result.views = this.views;
	result.record = this.record;
	return result;

    }

    
    
    /**
     *
     * create a new view from the source to target
     *
     */
    public View(Module source, Module target) 
    {
	this(null, source, target);
	throw new Error("don't allow empty view name");
    }
    
    /**
     *
     * create a view with the specified name
     *
     */
    public View(String name, Module source, Module target) {
      
	this.name = name;
	this.source = source;
	this.target = target;
	this.smodule = new Module(source.type, source.modName);
	this.tmodule = new Module(target.type, target.modName);

	try {
	    smodule.importModule(source);
	    tmodule.importModule(target);
	} catch (SignatureException e) {
	}
		 
	this.sortMap = new HashMap();
	this.opMap = new HashMap();
	this.varMap = new HashMap();
	this.trans = new HashMap();
    }


  public String getName() {
     return name;
  }


  public Module getSource() {
    return source;
  }


  public Module getTarget() {
    return target;
  }


  public Module getEnrichedSource() {
    return smodule;
  }

  public Module getEnrichedTarget() {
    return tmodule;
  }

 
  public Sort getTarget(Sort sort) {
      Iterator itor = sortMap.keySet().iterator();
      while (itor.hasNext()) {
	  Sort tmp = (Sort)itor.next();
	  if (sort.equals(tmp)) {
	      return (Sort)sortMap.get(tmp);
	  }
      }
      
      return null;
  }


  public Operation getTarget(Operation op) {

      Iterator itor = opMap.keySet().iterator();
      while (itor.hasNext()) {
	  Operation oper = (Operation)itor.next();
	  if (op.equals(oper)) {
	      return (Operation)opMap.get(oper);
	  }	  
      }

      return null;
  }


  public void addVariable(Variable var) throws ViewException {

      try {
	  smodule.addVariable(var);
	  
	  Sort sort = var.getSort();
	  sort = getTarget(sort);

	  if (sort != null) {

	      // there is a mapping in sortMap
	      Variable targetVar = new Variable(var.getName(), sort);
	      try {
		  tmodule.addVariable(targetVar);
		  varMap.put(var, targetVar); 
	      } catch (SignatureException e) {}
	      
	  } else if (tmodule.containsSort(var.sort)) {

	      // no mapping, but sort is contained in target
	      tmodule.addVariable(var);
	      varMap.put(var, var);
	      
	  } else if (smodule.getPrincipalSort().equals(var.sort) &&
		     sortMap.size() == 0){

	      // use the mapping between the principle sorts
	      sort = tmodule.getPrincipalSort();
	      Variable tvar = new Variable(var.name, sort);
	      tmodule.addVariable(tvar);
	      varMap.put(var, tvar);
	  }

      } catch (SignatureException e) {
	  throw new ViewException(e.getMessage());
      }

  }



    public boolean isMapTo(Sort from, Sort to) {
      
	Sort sort = getTarget(from);
	if (sort != null) {
	    return target.isSubsort(to, sort);
	} else if (from.equals(to)) {
	    return true;
	} else {
	    // not defined yet for sort mapping of from
	    sort = target.getSort(from);
	    if (sort != null) {
		return target.isSubsort(to,sort) || target.isSubsort(sort, to);
	    } else {
		return from.equals(to);
	    }
	}

    }



    public void addSortMap(Sort from, Sort to)
	throws ViewException
    {

	if (!allowSortDef) {
	    String msg = "A default mapping is defined alreday, no more "+
		" sort mapping can be defined";
	    throw new ViewException(msg);
	}

	if (!source.containsSort(from)) {
	    String msg = "Sort "+from.getName()+" not in source "+
		         source.getModuleName();
	    throw new ViewException(msg);
	}

	if (!target.containsSort(to)) {	    
	    String msg = "Sort "+to.getName()+
		         " not in target "+target.getModuleName();
	    throw new ViewException(msg);
	}

	Sort tmp = getTarget(from);
	if (tmp != null) {
	    if (!tmp.equals(to)) {
		throw new ViewException("A mapping for "+from.getName()+
					" already exists");
	    }
	} else {
	    sortMap.put(from,to);    
	}
     
    }


    
    public void addOperationMap(Operation from, Operation to)
	throws ViewException {
      
	if (!source.containsOperation(from)) {
	    String msg = "Operation "+from.getName()+" not in the source "+
	             source.getModuleName();
	    throw new ViewException(msg);
	}

	if (!target.containsOperation(to)) {
	    String msg = "Operation "+to.getName()+" not in the target "+
		         target.getModuleName();
	    throw new ViewException(msg);
	}

	Operation tmp = getTarget(from);
	if (tmp != null) {
	    if (!tmp.equals(to)) {
		throw new ViewException("A mapping for "+from.getName()+
					" already exists");
	    }
	} else {
	    if (sortMap.isEmpty()) {

		// use the mapping between the principal sorts
		if (allowSortDef) {
		    
		    allowSortDef = false;

		    // set sort mapping here
		    sortMap.put(source.getPrincipalSort(),
				target.getPrincipalSort());

		}

	    }

	    Sort[] args1 = from.getArgumentSorts();
	    Sort[] args2 = to.getArgumentSorts();

	    if (args1.length != args2.length) {
		throw new ViewException("The arities of the opeartions "+
					from.getCleanName()+" and "+
					to.getCleanName()+" are different");
	    } else {

		for (int i=0; i<args1.length; i++) {
		    Sort sort1 = args1[i];
		    Sort sort2 = args2[i];
		    if (!isMapTo(sort1, sort2)) {
			    sortMap.put(sort1, sort2);
			    /*
			    throw new ViewException("Sort "+sort1.getName()+
						    " is not mapped into "+sort2.getName());
			    */
		    }
		}

		Sort resSort1 = from.getResultSort();
		Sort resSort2 = to.getResultSort();
	     
		if (!isMapTo(resSort1, resSort2)) {

		    /*
		    if (resSort1.getName().equals(resSort2.getName())) {
			sortMap.put(resSort1, resSort2);
			opMap.put(from, to);
			return;
		    }

		    throw new ViewException(to.getCleanName()+
				  " is not of sort "+resSort1.getName()+"    "+resSort1.getModuleName());
		
		    */
		    sortMap.put(resSort1, resSort2);
		}
	    }
	    opMap.put(from,to);	
	}    
          
    }


    public void addTransformation(Term left, Term right) {
	trans.put(left, right);
    }


    public String toString() {
	String result = "";

	String sname = source.getModuleName().toString();
	String tname = target.getModuleName().toString();

	if (name == null) {
	    name = "";
	}

        String header = morphism? "   morph " : "   view ";
		
	if (sname.length() + tname.length() + name.length() + 12 > 80) {
	    result += header+name+"\n"+
		      "         from "+sname+"\n"+
		      "         to "+tname;
	} else if (name.length() > 0) {
	    result += header+name+" from "+sname+
		      " to "+tname;
        } else {
	    result += header+"from "+sname+" to "+tname;
	}

	result += " is \n";

	if (views.size() > 0 && morphism) {

	    result += "      [ \n";
	    for (int i=0; i<views.size(); i++) {
		View v = (View)views.get(i);
		
		String str = v.toString();
		StringTokenizer st = new StringTokenizer(str, "\n");
		while (st.hasMoreTokens()) {
		    result += "      "+st.nextToken()+"\n";
		}
		
	    }
	    result += "      ]\n";
	} 

	if (record.size() != 0) {
	    
	    Iterator itor = record.keySet().iterator();
	    while (itor.hasNext()) {
		Object key = itor.next();
		Object val = record.get(key);
		if (key instanceof Sort) {

		    Sort from = (Sort)key;
		    Sort to = (Sort)val;
		    result += "      sort "+source.toString(from)+
		              " to "+target.toString(to)+" .\n";  
		} 
	    }
	    
	    itor = record.keySet().iterator();
	    while (itor.hasNext()) {
		Object key = itor.next();
		Object val = record.get(key);
		if (key instanceof Operation) {
		    Operation from = (Operation)key;
		    Operation to = (Operation)val;
		    result += "      op "+from.getName()+
			      " to "+to.getName()+" .\n";
		}
	    }
	    
	    itor = record.keySet().iterator();
	    while (itor.hasNext()) {
		Object key = itor.next();
		Object val = record.get(key);
		if (key instanceof Term) {
		    Term from = (Term)key;
		    Term to = (Term)val;
		    result += "      op "+from+" to "+to+" .\n";
		}
	    }

	    result += "   endv\n";
	    
	    return result;
	}
	
	
	Variable[] vars = smodule.getVariables();
	for (int i=0; i<vars.length; i++) {
	    result += "      var "+vars[i].getName()+" : "+
		      vars[i].getSort().getName()+".\n";
	}

	Iterator itor = sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)sortMap.get(from);
	    if (from.getInfo().equals("system-default") &&
		from.equals(to)) {

	    } else {
		//result += "      sort "+source.toString(from)+
		//    " to "+target.toString(to)+" .\n";
		
		result += "      "+from+" to "+to+" .\n";
	    }
	}

	itor = opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)opMap.get(from);
	    if (from.info.equals("system-default") &&
		from.equals(to)) {

	    } else {
		result += "      op "+from.getName()+
		          " to "+to.getName()+" .\n";

                //result += "      "+from+"   "+from.modName+
		//          " to "+to+"    "+to.modName+" .\n";
		
	    }
	}

	itor = trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)trans.get(left);
	    result += "      op "+left+" to "+right+" .\n";
	}

	result += "   endv\n";

	return result;
    }



    public void validate() throws ViewException {
	
	for (int i=0; i<source.sorts.size(); i++) {
	    Sort from = (Sort)source.sorts.elementAt(i);
	    
	    if (sortMap.containsKey(from)) {
		continue;	       
		
	    } else if (from.equals(source.getPrincipalSort())) {

		sortMap.put(from, target.getPrincipalSort());
		continue;

	    } else if (target.containsSort(from)) {
		
		sortMap.put(from, from);
		continue;

	    } else {

		Sort[] sorts = target.getSortsByName(from.getName());
		if (sorts.length == 1) {
		    sortMap.put(from, sorts[0]);
		} else {
		    
		    Sort[] s = source.getDirectSubsorts(from);
		    if (s.length == 1) {
			Sort tmp = getTarget(s[0]);
			if (tmp != null) {
			    s = target.getDirectSupersorts(tmp);
			    if (s.length == 1) {
				sortMap.put(from, s[0]);
				continue;
			    }
			}
		    }
					    
		    int count = -1;
		    boolean done = false;
		    for (int j=2; j<target.sorts.size(); j++) {
			Sort to = (Sort)target.sorts.elementAt(j);
			ModuleName modName = to.getModuleName();
			
			if (!modName.hasNotation()) {
			    
			    if ( modName.op == modName.ATOM
				 &&
				 ( modName.atom.equals("INT")
				   ||
				   modName.atom.equals("NAT")
				 )
				 &&
				 ( target.containsSystemSort(IntModule.intSort)
				   ||
			    	   target.containsSystemSort(IntModule.natSort)
				 )
				) {
				continue;
			    }
				
			    count++;
			    
			    if (count == i-2) {
				sortMap.put(from, to);
				done = true;
				break;
			    }

			} else {

			    Sort tmp = (Sort)source.sorts.elementAt(j);
			    ModuleName tmpName = tmp.getModuleName();

			    if (tmpName.hasNotation() &&
				tmpName.atom.equals(modName.atom)) {
				count++;
			    }
			    			    
			}
			
		    }

		    if (!done) {
			throw new ViewException("no mapping for "+from+" in "+
						source.getModuleName(), 
						this);
		    }
		}
	    }

	}

	// check operations
	for (int i=0; i<source.operations.size(); i++) {
	    Operation from = (Operation)source.operations.elementAt(i);
	    	    
	    Iterator it = opMap.keySet().iterator();
	    boolean got = false;
	    while (it.hasNext()) {
		Operation o = (Operation)it.next();
		if (o.equals(from)) { 
		    got = true;
		    break;
		}	    
            }

            if (!got) {
		it = trans.keySet().iterator();
		while (it.hasNext()) {
		    
		    Term left = (Term)it.next();
		    if (left.operation.equals(from)) {
			got = true;
			break;
		    }
		}
	    }
	    
	    
	    // check mapping is defined
	    if (got) {
		continue;
	    } else  {
		
		Operation[] ops = target.getOperationsWithName(from.getName());
		ArrayList list = new ArrayList();
		for (int j=0; j<ops.length; j++) {

		    if (isAbleToMap(from, ops[j])) {
			list.add(ops[j]);
		    } 
		    
		}	
		
		if (list.size() == 1) {
		    opMap.put(from, list.get(0));
		    continue;
		} else {
		    
		    if (list.size() == 0) {

			// search by the from's signature 
			Sort[] args = new Sort[from.getArity()];
			for (int k=0; k<args.length; k++) {
			    args[k] = getTarget(from.argumentSorts[k]);
			}
			Sort resSort = getTarget(from.resultSort);
			ops = target.getOperations(args, resSort);
			
			if (ops.length == 1) {
			    opMap.put(from, ops[0]);
			    continue;
			} 			
		    } else {

			boolean done = false;
			for (int j=0; j<list.size(); j++) {
			    Operation tmp = (Operation)list.get(j);
			    if (getTarget(from.getResultSort()).equals(
			   	  tmp.getResultSort())) {
				opMap.put(from, tmp);
				done = true;
				break;
			    }
			}

			if (done) continue;
			
		    }
		    
		    
		    Iterator itor = trans.keySet().iterator();
		    boolean found = false;
		    while (itor.hasNext()) {
			Term term = (Term)itor.next();
			if (!term.isVariable() &&
			    term.getTopOperation().equals(from)) {
			    found = true;
			    break;
			}
		    }

		    if (!found) {
			throw new ViewException("no mapping for "+from,
						    this);
		    }
		
		}
	    }
	    
	}

    }


    private boolean isAbleToMap(Operation from, Operation to)
    {
	
	if (from.getArity() == to.getArity()) {
	    for (int i=0; i<from.getArity(); i++) {
		try {

		    Sort s1 = getTarget(from.getArgumentSortAt(i));
		    Sort s2 = getTarget(to.getArgumentSortAt(i));
		    
                    if (s1 == null) {
			sortMap.put(s1, s2);
		    } else if (s2 == null) {
			
		    } else if (!s1.equals(s2)) {
			return false;
		    } 
		    
		} catch (SignatureException e){
		}
	    }

	    return getTarget(from.getResultSort()).equals(to.getResultSort());
	    
	    // return true;
	} else {
	    return false;
	}
	
    }


    public Sort getImage(Sort sort) 
    {
	Sort result = getTarget(sort);
	if (result == null) {
	    return sort;
	} else {
	    return result;
	}
	
    }


    public Variable getImage(Variable var) 
    {
	return new Variable(var.getName(), getImage(var.getSort()));
    }
    
    

    public Operation getImage(Operation op) {
		
        Operation result = getTarget(op);
	if (result != null) {
	    return result;
	}

        Sort[] args = new Sort[op.getArity()];
        for (int i=0; i<args.length; i++) {
	    args[i] = getTarget(op.argumentSorts[i]);
	    if (args[i] == null) {
		args[i] = op.argumentSorts[i];
	    }
	}
	
        Sort res = getTarget(op.resultSort);
	if (res == null) {
	    res = op.resultSort;
	}	
	
	try {
	    result = new Operation(op.getName(), args, res, op.modName);
	    result.priority = op.priority;
	    result.info = op.info;
	    result.isAssociative = op.isAssociative;
	    result.isCommutative = op.isCommutative ;
	    result.isIdempotent =  op.isIdempotent ;
	    if (op.id != null) 
		result.id = getImage(op.id);
	    if (op.implicitId != null)
		result.implicitId = getImage(op.implicitId);
	    result.behavorial = op.behavorial;
	    result.gather = op.gather;
	    result.strategy = op.strategy;
	    	    
	} catch (SignatureException e) {
	}

	return result;
    }



    public Subsort getImage(Subsort subsort)
	throws SubsortException
    {

	Subsort result = new Subsort();
	
	Enumeration enumeration = subsort.subsorts.keys();
	while (enumeration.hasMoreElements()) {

	    Sort superSort = (Sort)enumeration.nextElement();
 	    Vector subs = (Vector)subsort.subsorts.get(superSort);
	    for (int i=0; i<subs.size(); i++) {
		Sort subSort = (Sort)subs.elementAt(i);
		result.addSubsort(getImage(superSort),
				  getImage(subSort));
  	    }
	}

	return result;
	
    }


    public Term getImage(Signature sig, Term term)
	throws TermException
    {
	
	if (trans.size() != 0) {
	    
	    Iterator iterator = trans.keySet().iterator();
	    while (iterator.hasNext()) {
		Term left = (Term)iterator.next();
		Term right = (Term)trans.get(left);
	 		
		Hashtable subst = term.getMatch(left, sig);
		if (subst != null) {
		    Hashtable newSubst = new Hashtable();
		    
		    Enumeration enum = subst.keys();
		    while (enum.hasMoreElements()) {
			Variable var = (Variable)enum.nextElement();
			Term trm = (Term)subst.get(var);
			trm = getImage(sig, trm);
						
			Iterator itor = varMap.keySet().iterator();
			boolean done = false;
			while (itor.hasNext()) {
			    Variable vtmp = (Variable)itor.next();
			    if (vtmp.equals(var)) {
				newSubst.put(varMap.get(vtmp), trm);
				done = true;
				break;
			    }
			}
			
		    }

		    return right.subst(newSubst, tmodule);
	          		    		    
		}
	    }	    
	}
	
	
	if (term.isVariable()) {
	    return new Term(getImage(term.var));
	} else {
	    Term[] terms = new Term[term.subterms.length];
	    for (int i=0; i<terms.length; i++) {
		terms[i] = getImage(sig, term.subterms[i]);
	    }

	    Operation op = getImage(term.operation);
	    return new Term(sig, op, terms);
	}
	
    }


    public Equation getImage(Signature sig, Equation eq)
 	throws TermException   
    {
	if (eq.condition != null) {
	    Equation tmp = new Equation(getImage(sig, eq.condition),
					getImage(sig, eq.left),
					getImage(sig, eq.right));
	    if (eq.name != null) {
		tmp.name = eq.name;
	    }
	    tmp.info = eq.info;
	    return tmp;
	    
	} else {
	   Equation tmp =  new Equation(getImage(sig, eq.left),
					getImage(sig, eq.right));
	   if (eq.name != null) {
	       tmp.name = eq.name;
	   }
	    tmp.info = eq.info;
	   return tmp;
	}
    }
    

    
    public Module getImage(Module module)
	throws SubsortException, TermException, SignatureException
    {
	
	Module result = new Module(module.type, module.modName);
	
	// add sort
	for (int i=0; i<module.sorts.size(); i++) {
	    Sort sort = (Sort)module.sorts.elementAt(i);
	    sort = getImage(sort);
	    	    
	    if (!result.containsSort(sort)) {
		result.addSort(sort);
	    }
	}

	// add subsorts
	result.subsorts = getImage(module.subsorts);

	// add variables
	for (int i=0; i<module.vars.size(); i++) {
	    Variable var = (Variable)module.vars.elementAt(i);
	    var = getImage(var);
	    
	    if (!result.containsVariable(var)) {
		result.addVariable(var);
	    }
	}	

	// add operations
	for (int i=0; i<module.operations.size(); i++) {
	    Operation op = (Operation)module.operations.elementAt(i);

	    if (op.isConstant()) {
		try {
		    Term term = new Term(op);
		    boolean done = false;
		    Iterator itor = trans.keySet().iterator();
		    while (itor.hasNext()) {
			Term tmp = (Term)itor.next();
			if (term.equals(tmp)) {
			    done = true;
			    break;    
			}
		    }

		    if (done) continue;
		} catch (Exception e){
		}
	    } else {
		boolean done = false;
		Iterator itor = trans.keySet().iterator();
		while (itor.hasNext()) {
		    Term tmp = (Term)itor.next();
		    if (tmp.operation.equals(op)) {
			done = true;
		    }
		}		
		if (done) continue;
	    }
	   	    
	    op = getImage(op);
	    
	    if (!result.containsOperation(op)) {
		result.addOperation(op);
	    }
	}	
	    
	// add equation
	for (int i=0; i<module.equations.size(); i++) {
	    Equation eq = (Equation)module.equations.get(i);

	    eq = getImage(result, eq);
	    if (!result.containsEquation(eq)) {
		result.equations.add(eq);
	    }	    
	}

	// add general equations
	for (int i=0; i<module.generalEquations.size(); i++) {
	    Equation eq = (Equation)module.generalEquations.get(i);
	    eq = getImage(result, eq);
	    if (!result.generalEquations.contains(eq)) {
		result.generalEquations.add(eq);
	    }	    
	}	

	// handle alias
	Iterator itor = module.alias.keySet().iterator();
	while (itor.hasNext()) {
	    String key = (String)itor.next();
	    ArrayList list = (ArrayList)module.alias.get(key);
	    List res = new ArrayList();

	    for (int i=0; i<list.size(); i++) {
		Sort sort = (Sort)list.get(i);
		res.add(getImage(sort));
	    }
	    	
	    result.alias.put(key, res);
	}
	
	return result;
	
    }



    public View getImage(View view)
	throws TermException, SignatureException,
	       SubsortException, ViewException
    {

	Module newSource = this.getImage(view.source);
	Module newTarget = this.getImage(view.target);
	View result = new View("", newSource, newTarget);

	Iterator itor = view.sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)view.sortMap.get(from);
	    result.addSortMap(getImage(from), getImage(to));    
	}

	itor = view.opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)view.opMap.get(from);
	    result.addOperationMap(getImage(from), getImage(to));	    
	}

	itor = view.trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)view.trans.get(left);
	    result.addTransformation(getImage(newSource, left),
				     getImage(newTarget, right));
	}
	
	
	return result;
    }
    
    

    protected View addNotation(String notation, String flag, Map env) 
	throws ViewException, SignatureException
    {
	
	View result;

	if (flag == null) {
	    result = new View(name,
			      source.addAnnotation(notation, env),
			      target);
        } else {
	    result = new View(name,source.addAnnotation(notation, env),
			      target.addAnnotation(flag, env));
	}

		    
       	Variable[] vars = smodule.getVariables();
	for (int i=0; i<vars.length; i++) {
	    result.addVariable(vars[i].addAnnotation(notation, env));
	}

	Iterator itor = sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)sortMap.get(from);
	    
	    from = from.addAnnotation(notation, env);
	    if (flag != null) {
		to = to.addAnnotation(flag, env);
	    }
	    result.addSortMap(from, to);
	    
	}

	itor = opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)opMap.get(from);

	    from = from.addAnnotation(notation, env);
            if (flag != null) {
		to = to.addAnnotation(flag, env);
	    }
	    
	    try {
		result.addOperationMap(from, to);
	    } catch (Exception e) {
	    }
	    
	}
	

	itor = trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)trans.get(left);
	    left = left.addAnnotation(notation, smodule, env);
	    result.addTransformation(left, right);
	} 

        return result;
    }


    protected void record(Module module) 
    {
	main = module;
    }
    


    public View instanceBy(Module[] mods, String[] notations, Map env) 
	throws ViewException  
    {

	try {

	    List list = new ArrayList();
	    
	    // create new module name
	    ModuleName[] modNames = new ModuleName[mods.length];
	    for (int i=0; i<mods.length; i++) {
		if (notations[i] != null) {
		    modNames[i] = new ModuleName(notations[i]);
		} else {
		    //modNames[i] = mods[i].getModuleName();
		    View view = (View)mods[i].getProperty("view");
		    modNames[i] = new ModuleName(view.name);
		    modNames[i].view = view;
		    
		}

		list.add(modNames[i]);	
	    }

	    ModuleName modName1 = (ModuleName)source.modName;
            if (source.modName.subexps.size() > 0) {
                modName1 = (ModuleName)source.modName.subexps.get(0);
            }      
	    ModuleName sourceModName =  modName1.instance(list);

	    ModuleName modName2 = (ModuleName)target.modName.subexps.get(0);
	    ModuleName targetModName = modName2.instance(list);
	    
	    // check the size of actual parameters
	    if (mods.length != main.paraModules.size() || 
		notations.length != main.paraModules.size() ) {
		throw new ViewException("expect "+main.paraModules.size()+
					" parameters");
	    }

	    // create new source and target
	    Module newSource = (Module)source.clone();
	    Module newTarget = (Module)target.clone();
	    
	    View[] views = new View[mods.length];
	    for (int i=0; i<mods.length; i++) {
	    	    
		// get parameter and its name
		Module parameter = (Module)main.paraModules.get(i);
		String paraName = (String)main.paraNames.get(i);

		// create an view 
		views[i] = (View)mods[i].getProperty("view");
   
		if (views[i] == null) {
		    views[i] = mods[i].getViewFor(parameter);
		}
	   
		if (views[i] == null) {
		    throw new ViewException(mods[i].getModuleName()+
					    " is not an instance of "+
					    parameter.getModuleName());
		}

		views[i] = views[i].addNotation(paraName, notations[i], env);
                newSource = views[i].getImage(newSource);	
		newTarget = views[i].getImage(newTarget);		
		
		ModuleName tmpName =
		    parameter.modName.addAnnotation(paraName);
		ModuleName newSourceName =
		    newSource.modName.changeModuleName(tmpName,
						       modNames[i]);
		newSource = newSource.changeModuleName(tmpName,
						       modNames[i],
						       newSourceName);

		ModuleName newTargetName =
		    newTarget.modName.changeModuleName(tmpName,
						       modNames[i]);
		newTarget = newTarget.changeModuleName(tmpName,
						       modNames[i],
						       newTargetName);
       
		if (notations[i] == null) {
		    newSource.importModule(mods[i]);
		    newTarget.importModule(mods[i]);
		}

		// notations[i] is not null, it simply means
		// the actual parameter is a parameter of this module
		// thus, do nothing in this case

	    }    

	    String viewName = this.name+"[";
	    for (int i=0; i<mods.length; i++) {
		if (i == 0) {
		    viewName += ((View)mods[i].getProperty("view")).name;
		} else {
		    viewName += ", "+((View)mods[i].getProperty("view")).name; 
		}
	    }
	    viewName += "]";
	    
	    View result = new View(viewName, newSource, newTarget);
            
            
	    // handle sort mapping
	    Iterator itor = sortMap.keySet().iterator();
	    while (itor.hasNext()) {
		
		Sort from = (Sort)itor.next();
		Sort to = (Sort)sortMap.get(from);
		
		// change module names
		for (int i=0; i<mods.length; i++) {
	    	    
		    // get parameter and its name
		    Module parameter = (Module)main.paraModules.get(i);
		    String paraName = (String)main.paraNames.get(i);

		    ModuleName tmpName =
			parameter.modName.addAnnotation(paraName);
		
                    from = views[i].getImage(from);
		    from = from.changeModuleName(tmpName, modNames[i]);

		    to = views[i].getImage(to);
		    to = to.changeModuleName(tmpName, modNames[i]);
		    
		}

		result.addSortMap(from, to);
	    }

	    itor = opMap.keySet().iterator();
	    while (itor.hasNext()) {
		Operation from = (Operation)itor.next();
		Operation to = (Operation)opMap.get(from);

		for (int i=0; i<mods.length; i++) {

		    // get parameter and its name
		    Module parameter = (Module)main.paraModules.get(i);
		    String paraName = (String)main.paraNames.get(i);

		    ModuleName tmpName =
			parameter.modName.addAnnotation(paraName);
		    from = views[i].getImage(from);
		    from = from.changeModuleName(tmpName, modNames[i]);

		    to = views[i].getImage(to);
		    to = to.changeModuleName(tmpName, modNames[i]);
		    
		}
		result.addOperationMap(from, to);
	    }
	   
	    itor = trans.keySet().iterator();
	    while (itor.hasNext()) {
		Term from = (Term)itor.next();
		Term to = (Term)trans.get(from);
				
		for (int i=0; i<views.length; i++) {

		    // get parameter and its name
		    Module parameter = (Module)main.paraModules.get(i);
		    String paraName = (String)main.paraNames.get(i);

		    ModuleName tmpName =
			parameter.modName.addAnnotation(paraName);
		    from = views[i].getImage(newSource, from);
		    from = from.changeModuleName(tmpName,
						 modNames[i],
						 newSource);

		    to = views[i].getImage(newTarget, to);
		    to = to.changeModuleName(tmpName, modNames[i], newTarget);

		}

		result.addTransformation(from, to);

	    }
	    return result;

	} catch (Exception e) {
	    //e.printStackTrace();
	    throw new ViewException(e.getMessage());
	}

    }


    public View aliasModuleName(String alias)
	throws SignatureException, ViewException
    {
	ModuleName modName = new ModuleName(alias);
	modName.subexps.add(this.source.modName);
	Module newSource = this.source.changeModuleName(source.modName,
							modName,
							modName);
	Module newTarget = this.target.changeModuleName(target.modName,
							modName,
							modName);
	
	View result = new View("", newSource, newTarget);

	Iterator itor = this.sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)this.sortMap.get(from);

	    from = from.changeModuleName(source.modName,modName);
	    to = to.changeModuleName(target.modName,modName);
	    
	    result.addSortMap(from, to);
	    
	}

	itor = this.opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)this.opMap.get(from);
	    from = from.changeModuleName(source.modName,modName);
	    to = to.changeModuleName(target.modName,modName);
	    result.addOperationMap(from, to);	    
	}

	itor = this.trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)this.trans.get(left);
	    left = left.changeModuleName(source.modName, modName, newSource);
	    right = right.changeModuleName(target.modName,modName,newTarget);
	    result.addTransformation(left, right);
	}
	
	return result;
	
    }



    public View sum(View view)
	throws ViewException, SignatureException
    {
	Module resSource = this.source.sum(view.source);
	Module resTarget = this.target.sum(view.target);

	View result = new View("", resSource, resTarget);

	// copy all in this to resView
	
	Iterator itor = this.sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)this.sortMap.get(from);
	    result.addSortMap(from, to);    
	}

	itor = this.opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)this.opMap.get(from);
	    result.addOperationMap(from, to);	    
	}

	itor = this.trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)this.trans.get(left);
	    result.addTransformation(left, right);
	}

	// copy and check view
	itor = view.sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)view.sortMap.get(from);

	    Sort tmp = (Sort)this.sortMap.get(from);
	    if (tmp != null && !tmp.equals(to)) {
		throw new ViewException("inconsistent sort mapping for "+
					from.getName());
	    }
	    
	    result.addSortMap(from, to);    
	}

	itor = view.opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)view.opMap.get(from);

	    Operation tmp = (Operation)this.opMap.get(from);
	    if (tmp != null && !tmp.equals(to)) {
		throw new ViewException("inconsistent operator mapping for "+
					from.getName());
	    }
	    
	    result.addOperationMap(from, to);	    
	}

	itor = view.trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)view.trans.get(left);

	    Term tmp = (Term)this.trans.get(left);
	    if (tmp != null && !tmp.equals(right)) {
		throw new ViewException("inconsistent mapping for "+
					left);
	    }	    
	    
	    result.addTransformation(left, right);
	}	
	
	return result;
    }
    

    
    public View rename(Map map)
	throws SignatureException, ViewException
    {
	Module resSource = (Module)this.source.clone();
	Module resTarget = (Module)this.target.clone();

	Map map1 = new HashMap();
	Map map2 = new HashMap();
	Map record = new HashMap();
	
	Iterator itor = map.keySet().iterator();
	while (itor.hasNext()) {
	    Object obj = itor.next();
	    if (obj instanceof Sort) {

		// do something on resSource
		Sort from = (Sort)obj;
                Sort to = (Sort)map.get(from);
		resSource = resSource.changeSort(resSource.modName,
						 from,
						 to);
                map1.put(from, to);
		Sort sort = to;
		
		// do something on resTarget		
		from = this.getTarget(from);				
		to = new Sort(to.getName(), from.getModuleName());
		resTarget = resTarget.changeSort(resTarget.modName,
						 from,
						 to);
                map2.put(from, to);

		record.put(sort, to);
				
	    } else {

		// do something on resSource
		Operation from = (Operation)obj;
                Operation to = (Operation)map.get(from);
		resSource = resSource.replaceOperation(resSource.modName,
						       from,
						       to);
                map1.put(from, to);
		Operation op = to;
				
		// do something on resTarget		
		from = this.getTarget(from);
		to = new Operation(to.getName(),
				   from.getArgumentSorts(),
				   from.getResultSort(),
				   from.modName);

		resTarget = resTarget.replaceOperation(resTarget.modName,
						       from,
						       to);
                map2.put(from, to);		
		record.put(op, to);
	    }
	    
	}

	ModuleName name1 = resSource.modName.renaming(map1);
	ModuleName name2 = resTarget.modName.renaming(map2);

        resSource = resSource.changeModuleName(resSource.modName,
					       name1,
					       name1);
	
        resTarget = resTarget.changeModuleName(resTarget.modName,
					       name2,
					       name2);	
        
        View result = new View("", resSource, resTarget);


	itor = record.keySet().iterator();
	while (itor.hasNext()) {
	    Object obj = itor.next();
	    if (obj instanceof Sort) {
		Sort from = (Sort)obj;
		Sort to = (Sort)record.get(from);
		from = from.changeModuleName(source.modName, name1);
		to = to.changeModuleName(target.modName, name2);
		result.sortMap.put(from, to);
	    } else {
		Operation from = (Operation)obj;
		Operation to = (Operation)record.get(from);
		from = from.changeModuleName(source.modName, name1);
		to = to.changeModuleName(target.modName, name2);
		result.opMap.put(from, to);		
	    }
	    
	}

	
	itor = this.sortMap.keySet().iterator();
	while (itor.hasNext()) {
	    Sort from = (Sort)itor.next();
	    Sort to = (Sort)this.sortMap.get(from);

	    boolean found = false;
	    Iterator i = map.keySet().iterator();
	    while (i.hasNext()) {
		Object obj = i.next();
		if (obj instanceof Sort) {
		    Sort tmp = (Sort)obj;
		    if (from.equals(tmp)) {
			found = true;
			break;
		    }
		}
		
	    }
	    
	    if (found) {
		
	    } else {
		from = from.changeModuleName(source.modName, name1);
		to = to.changeModuleName(target.modName, name2);
		result.addSortMap(from, to);
	    }
	    
	}

	itor = this.opMap.keySet().iterator();
	while (itor.hasNext()) {
	    Operation from = (Operation)itor.next();
	    Operation to = (Operation)this.opMap.get(from);
	    	    
	    if (map.containsKey(from)) {
		
	    } else {

		Iterator i = map1.keySet().iterator();
		while (i.hasNext()) {
		    Object tmp = i.next();
		    if (tmp instanceof Sort) {
			Sort sort = (Sort)tmp;
			Sort dest = (Sort)map1.get(sort);
			from = from.changeSort(sort, dest);
		    } else {
			Operation op = (Operation)tmp;
			Operation dest = (Operation)map1.get(op);
			from = dest;
		    }
		}

		i = map2.keySet().iterator();
		while (i.hasNext()) {
		    Object tmp = i.next();
		    if (tmp instanceof Sort) {
			Sort sort = (Sort)tmp;
			Sort dest = (Sort)map2.get(sort);
			to = to.changeSort(sort, dest);
		    } else {
			Operation op = (Operation)tmp;
			Operation dest = (Operation)map2.get(op);
			to = dest;
		    }
		}		
		
		from = from.changeModuleName(source.modName, name1);
		to = to.changeModuleName(target.modName, name2);
		result.addOperationMap(from, to);
				
	    }	    	    
	}

	itor = this.trans.keySet().iterator();
	while (itor.hasNext()) {
	    Term left = (Term)itor.next();
	    Term right = (Term)this.trans.get(left);

            Iterator i = record.keySet().iterator();
	    //result.addTransformation(left, right);
	}
	
	return result;
	
    }


    public View composite(View view) 
	throws ViewException, TermException
    {
	if (this.target.modName.equals(view.source.modName)) {

	    String resName;
	    
	    if (this.name != null && !this.name.equals("")) {

		if (this.isIdentity()) {

		    resName = view.name;
		    		    
		} else if (this.name.equals(target.modName.toString()) &&
		    this.target.modName.op == ModuleName.ANNOTATE &&
		    this.source.modName.equals(
			 (ModuleName)this.target.modName.subexps.get(0))) {
		    if (view.name != null && !view.name.equals("")) {
			resName = view.name;
		    } else {
			resName = view.target.modName.toString();
		    }
		} else {
		    
		    if (view.name != null && !view.name.equals("")) {
			resName = this.name+" * "+view.name;
		    } else {
			resName = this.name;
		    }
		}
		
	    } else if (view.name != null && !view.name.equals("")) {
		resName = view.name;
	    } else {
		resName = view.target.modName.toString();
	    }
	    
	    View result = new View(resName,
				   source,
				   view.target);

	    Iterator itor = this.sortMap.keySet().iterator();
	    while (itor.hasNext()) {
		Sort from = (Sort)itor.next();
		Sort to = (Sort)this.sortMap.get(from);
		result.addSortMap(from, view.getTarget(to));    
	    }

	    itor = this.opMap.keySet().iterator();
	    while (itor.hasNext()) {
		Operation from = (Operation)itor.next();
		Operation to = (Operation)this.opMap.get(from);
		Operation newTo = view.getTarget(to);
		if (newTo == null) {

		    /*
		    Iterator it = view.trans.keySet().iterator();
		    Term left=null, right=null;
		    while (it.hasNext()) {
			Term left = (Term)itor.next();
			Term right = (Term)view.trans.get(left);
			if (left.operation.equals(newTo)) {
			    break;
			}
		    }
		    */
		    
		    Term fromTerm=null, toTerm=null;
		    if (from.isConstant()) {
			fromTerm = new Term(from);
			toTerm = new Term(to);
		    }
		    		    
		    toTerm = view.getImage(result.smodule, toTerm);
		    result.addTransformation(fromTerm, toTerm);

		} else {
		    result.addOperationMap(from, newTo);
		}
		
		
	    }

	    itor = this.trans.keySet().iterator();
	    while (itor.hasNext()) {
		Term left = (Term)itor.next();
		Term right = (Term)this.trans.get(left);
		result.addTransformation(left, view.getImage(result.smodule,
							     right));
	    }
	    
	    return result;
	    
	} else {
	    throw new ViewException("can not make composition of the views: "+
				    target.modName+" with "+
				    view.source.modName);
	}
	
    }


    public boolean isIdentity() 
    {
	
	if (name.equals(target.modName.toString())) {

	    ModuleName mn1 = source.modName;
	    ModuleName mn2 = target.modName;
	    if (source.modName.op == ModuleName.ANNOTATE) {
		mn1 = (ModuleName)source.modName.subexps.get(0);
	    } 
	    
	    if (target.modName.op == ModuleName.ANNOTATE) {
		mn2 = (ModuleName)target.modName.subexps.get(0);
	    }

	    if (mn1.equals(mn2)) {
		return true;
	    } else {
		return false;
	    }
	    
	} else {
	    return false;
	}
	
    }


    /*
    public View changeNotation(String from, String to) {
        
        Module nsrc = source.changeParameterName(from, to);
	Module ntgt = target.changeParameterName(from, to);
        
        String nname = name;
	if (name.equals(target.modName().toString())) {
	    nname = target.modName().toString();
	}

	View result = new View(nname, nsrc, ntgt);
	result.nmain = main.changeParameterName(from, to);
        result.morphism = morphism;
        result.smodule = smodule.changeParameterName(from, to);
	result.tmodule = tmodule.changeParameterName(from, to);
	result.allowSortDef = allowSortDef;

    Map sortMap, opMap, varMap, trans;
    ArrayList views = new ArrayList();
    HashMap record = new HashMap();
  
    }
    */

}
























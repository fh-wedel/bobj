
package bobj;

import java.util.*;

public class CaseModule extends Module 
{
    ModuleName name, base;
    Term context, cond;
    ArrayList cases;
    ArrayList labels;
    static String errMsg;
    int handledCases, failedCases;
        
    public CaseModule(ModuleName name, ArrayList list)
	throws CaseModuleException 
    {

        this(name, (Module)list.get(0));

	CaseModule mod = (CaseModule)list.get(0);
        this.base = mod.base;
	this.context = mod.context;
		
	// check and input variables
	ArrayList tmpCases = new ArrayList();
	tmpCases.add(mod.cases);

	ArrayList tmpLabels = new ArrayList();
	if (mod.labels.size() == 0) {
	    ArrayList tmp = new ArrayList();
	    for (int i=0; i<mod.cases.size(); i++) {
		tmp.add(String.valueOf(i+1));
	    }
	    tmpLabels.add(tmp);
	} else {
	    tmpLabels.add(mod.labels);
	}

	for (int j=0; j<mod.vars.size(); j++) {
	    Variable var = (Variable)mod.vars.elementAt(j);
	    if (!this.containsVariable(var)) {
		try {
		    this.addVariable(var);
		} catch (SignatureException e) {
		    throw new CaseModuleException(e.getMessage());
		}
	    }
	}
	
	for (int i=1; i<list.size(); i++) {
	    mod = (CaseModule)list.get(i);
	    
	    if (!mod.base.equals(base)) {
		throw new CaseModuleException(mod.name+" is not on the base "+
					      base);
	    }

	    if (!mod.context.equals(context) &&
		!mod.context.isSubterm(context)) {
		throw new CaseModuleException(mod.context+
					      " is not coherent to "+context);
	    }

	    for (int j=0; j<mod.vars.size(); j++) {
		Variable var = (Variable)mod.vars.elementAt(j);
		if (!this.containsVariable(var)) {
		    try {
			this.addVariable(var);
		    } catch (SignatureException e) {
			throw new CaseModuleException(e.getMessage());
		    }
		}
	    }

	    tmpCases.add(mod.cases);
	    if (mod.labels.size() == 0) {
		ArrayList tmp = new ArrayList();
		for (int j=0; j<mod.cases.size(); j++) {
		    tmp.add(String.valueOf(j+1));
		}
		tmpLabels.add(tmp);
	    } else {
		tmpLabels.add(mod.labels);
	    }
	}

	ArrayList resLabels = new ArrayList();
	this.cases = makeCases(tmpCases, tmpLabels, resLabels);
	this.labels = resLabels;
	
    }
    
    
    public CaseModule(ModuleName name, Module module) 
    {
	super(Module.INITIAL, name);
	
	this.name = name;
	this.base = module.modName;
	this.cases = new ArrayList();
	this.labels = new ArrayList();
	
	Module tmp = (Module)module.clone();

	// clone signature part
	this.sorts = (Vector)tmp.sorts.clone();
        this.subsorts = (Subsort)tmp.subsorts.clone();
        this.operations = (Vector)tmp.operations.clone();
        this.tokens = (Vector)tmp.tokens.clone();
        this.compatible = (Hashtable)tmp.compatible.clone();
        this.alias = (HashMap)tmp.alias.clone();
        this.parameters = tmp.parameters;
	this.firsts = (ArrayList)(tmp.firsts.clone());
	this.lasts = (ArrayList)(tmp.lasts.clone());	
	this.balancedBrackets = tmp.balancedBrackets;
	this.explicitRetract = tmp.explicitRetract;
	
	
	// clone module parts
	this.paraModules = (ArrayList)(tmp.paraModules.clone());
	this.paraNames = (ArrayList)(tmp.paraNames.clone());
	this.protectImportList = (ArrayList)(tmp.protectImportList.clone());
	this.extendImportList = (ArrayList)(tmp.extendImportList.clone());
	this.useImportList = (ArrayList)(tmp.useImportList.clone());
	
	this.equations = new ArrayList();
	Iterator itor = tmp.equations.iterator();
	while (itor.hasNext()) {
	    Equation eq = (Equation)itor.next();
	    this.equations.add(eq);
	}

	this.generalEquations = new ArrayList();
	itor = tmp.generalEquations.iterator();
	while (itor.hasNext()) {
	    Equation eq = (Equation)itor.next();
	    this.generalEquations.add(eq);
	}	
	
	this.props = (HashMap)(tmp.props.clone());
	
    }
    

    public void setContext(Term term) 
    {
	this.context = term;
    }


    public String toString() 
    {
	String result = "";
        result = "cases "+name+" for "+base+" is \n";

	// handle variables
	Enumeration e = sorts.elements();
	while (e.hasMoreElements()) {
	    Sort tmp = (Sort)e.nextElement();
	    if (tmp.getInfo().equals("system-default")) {
		continue;
	    }
	    Variable[] vars = getVariablesOnSort(tmp);
	    if (vars.length == 1) {
		result += "   var ";
	    } else if (vars.length > 1) {
		result += "   vars ";
	    }
	    
	    for (int i=0; i<vars.length; i++) {
		result += vars[i].name+" ";
	    }

	    if (vars.length > 0) {
		result += ": "+toString(tmp)+" .\n";
	    }    
	}

	// context
	result += "   context "+context+" .\n";

	// cases
	for (int i=0; i<cases.size(); i++) {
	    if (labels.size() > 0) {
		result += "   case ("+labels.get(i)+") :\n";
	    } else {
		result += "   case \n";
	    }

	    ArrayList list = (ArrayList)cases.get(i);
	    for (int j=0; j<list.size(); j++) {
                Object obj = list.get(j);
		if (obj instanceof Operation) {
		    result += "     "+this.toString((Operation)obj)+" .\n";

		} else {
		    result += "     "+list.get(j)+" .\n";
		}
	    }
	}

	result += "end\n";
	
	return result;
    }


    private ArrayList makeCases(ArrayList list,
				ArrayList llist,
				ArrayList res) 
    {
	    
	ArrayList result = new ArrayList();
	
	if (list.size() == 1) {
	    ArrayList tmp = (ArrayList)list.get(0);
	    result = (ArrayList)tmp.clone();

	    ArrayList ltmp = (ArrayList)llist.get(0);
	    res.addAll(ltmp);

	    return result;
	}

	ArrayList copy = (ArrayList)list.clone();
	ArrayList first = (ArrayList)copy.get(0);
	copy.remove(0);

	ArrayList lcopy = (ArrayList)llist.clone();
	ArrayList lfirst = (ArrayList)lcopy.get(0);
	lcopy.remove(0);
		
	ArrayList ltmp = new ArrayList();
	ArrayList tmp = makeCases(copy, lcopy, ltmp);
        for (int i=0; i<first.size(); i++) {
	    for (int j=0; j<tmp.size(); j++) {
		ArrayList element = (ArrayList)first.get(i);
		ArrayList aCase = (ArrayList)tmp.get(j);
		ArrayList mid = new ArrayList();
		mid.addAll(element);
		mid.addAll(aCase);
		result.add(mid);
	    }
	}

        for (int i=0; i<lfirst.size(); i++) {
	    for (int j=0; j<ltmp.size(); j++) {
		String aStr = (String)lfirst.get(i);
		String bStr = (String)ltmp.get(j);
		res.add(aStr+","+bStr);
	    }
	}
	
	return result;

    }


    public void remove(String label) 
	throws CaseModuleException
    {
	
	if (this.labels.isEmpty()) {
	    try {
		int i = Integer.parseInt(label);
		cases.remove(i-1);
	    } catch (Exception e) {
		throw new CaseModuleException("no case in "+name+" with name "+
					      label);
	    }
	} else {
	    if (labels.contains(label)) {

		int i = labels.indexOf(label);
		cases.remove(i);
		labels.remove(i);

	    } else {

                if (label.indexOf("*") != -1) {
		    
		    for (int k=labels.size()-1; k>=0; k--) {
			String tmp = (String)labels.get(k);
			if (match(label, tmp)) {
			    cases.remove(k);
			    labels.remove(k);
			}
		    }

		} else {
		    throw new CaseModuleException("no case in "+name+
						  " with name "+
						  label);
                }		
	    }
	    
	}
	
    }
    
    
    static private boolean match(String pattern, String string) {

	boolean result = true;

	StringTokenizer st1 = new StringTokenizer(pattern, ",");
	StringTokenizer st2 = new StringTokenizer(string, ",");

	while (st1.hasMoreTokens()) {
	    String s1 = st1.nextToken();
	    String s2 = st2.nextToken();
	    if (s1.equals("*")) {
		continue;
	    } else if (!s1.equals(s2)) {
                return false;
	    }
        }

        return result;

    }

}
















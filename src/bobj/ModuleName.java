
package bobj;

import java.util.*;

public class ModuleName
{
    final public static int ATOM = 0;
    final public static int INSTANCE = 1;
    final public static int ANNOTATE = 2;
    final public static int SUM = 3;
    final public static int RENAMING = 4;
    final public static int GENERAL_INSTANCE = 5;    
    
    int op;
    String atom;
    List subexps;
    View view;
    
    protected ModuleName() {
	this.subexps = new ArrayList();
    }

    
    public ModuleName(String name) {
        this.op = ATOM;
        this.atom = name;
	this.subexps = new ArrayList();

	if (name.indexOf(":") != -1) {
	    throw new Error("what: "+name);
	}
	
	
    }

    
    public ModuleName instance(ModuleName[] mods) 
    {
	ModuleName result = new ModuleName();
	result.op = INSTANCE;
	result.subexps.add(this);
	for (int i=0; i<mods.length; i++) {
	    result.subexps.add(mods[i]);
	}
	return result;
    }


    public ModuleName instance(List list) 
    {
	ModuleName result = new ModuleName();
	result.op = GENERAL_INSTANCE;
	result.subexps.add(this);
	result.subexps.addAll(list);
	return result;	
    }
    

    public ModuleName addAnnotation(String name) {
	
        if (hasSameRoot(name)) {
	    return this;
	}
	
	ModuleName result = new ModuleName();
	result.op = ANNOTATE;
	result.atom = name;
	result.subexps.add(this);
	return result;	
    }


    private boolean hasSameRoot(String name) 
    {
	if (this.op == GENERAL_INSTANCE) {
	    ModuleName mname = (ModuleName)subexps.get(0);
	    if (mname.op == ANNOTATE &&
		mname.atom.equals(name)) {
		return true;
	    }
	}
	return false;
	
    }
    

    
    public ModuleName sum(ModuleName modName) 
    {
 	ModuleName result = new ModuleName();
	result.op = SUM;
	result.subexps.add(this);
	result.subexps.add(modName);
	return result;	 
    }


    public ModuleName renaming(Map map) 
    {
	
	ModuleName result = new ModuleName();
	result.op = RENAMING;
	result.subexps.add(this);
	result.subexps.add(map);

	return result;
    }
    

    
    public boolean hasNotation() {
	return op == ANNOTATE;
	
    }


    public boolean hasNotation(String name) {
		
	if (op == ANNOTATE && atom.equals(name)) {
	    return true;
	} else if (op == GENERAL_INSTANCE) {
	    	    
	    ModuleName mname =(ModuleName)subexps.get(0);
	    if (mname.atom.equals(name)) {
		return true;
	    }

	    // for bug fix 2002-6-10
	    for (int i=1; i<subexps.size(); i++) {
		Object obj = subexps.get(i);
		if (obj instanceof ModuleName) {
		    mname =(ModuleName)obj;
		    if (mname.hasNotation(name)) {
			return true;
		    }
		} else if (obj instanceof View) {
		    View view = (View)obj;
		    if (view.name.equals(view.target.modName.toString())) {
			return true;
		    }
		}
	    }
	    
	    return false;
	} else {
	    return false;
	}
    }

    
    public boolean hasNotation(String[] names) {
	for (int i=0; i<names.length; i++) {
	    if (hasNotation(names[i])) {
		return true;
	    } 
	}
	return false;
    }
    
    public ModuleName getOriginModuleName() {
	if (op == ANNOTATE) {
	    return (ModuleName)subexps.get(0);
	} else {
	    return this;
	}
    }

    
    public String toString() 
    {
	String result = "";

	switch (op) {
	case ATOM:
	    result += atom;
	    break;
        case ANNOTATE:
	    result += "("+atom+":"+subexps.get(0)+")";
	    break;
	case SUM:
	    result += subexps.get(0)+" + "+ subexps.get(1);
	    break;
	case INSTANCE:
	    result += (ModuleName)subexps.get(0);
	    result += "[";
	    for (int i=1; i<subexps.size(); i++) {
                if (i>1) {
		    result += ", ";
		}
		
		result += subexps.get(i);
	    }
	    result += "]";
	    break;
	case GENERAL_INSTANCE :
	    result += (ModuleName)subexps.get(0);
	    result += "[";
	    for (int i=1; i<subexps.size(); i++) {
                if (i>1) {
		    result += ", ";
		}

		Object obj = subexps.get(i);
		if (obj instanceof View) {
		    result += ((View)obj).name;
		} else {
		    result += subexps.get(i);
		}
		
	    }
	    result += "]";
	    break;	    
	case RENAMING:
	    result += "("+(ModuleName)subexps.get(0)+")";
	    result += " * (";

	    boolean begin = true;
	
	    Map map = (Map)subexps.get(1);
	    Iterator itor = map.keySet().iterator();
	    while (itor.hasNext()) {
		Object obj = itor.next();
		if (obj instanceof Sort) {
		    Sort from = (Sort)obj;
		    Sort to = (Sort)map.get(from);
		    if (!begin) {
			result += ", ";
		    } else {
			begin = false;
		    }
		    result += "sort "+from.getName()+" to "+to.getName();
		} else {
		    Operation from = (Operation)obj;
		    Operation to = (Operation)map.get(from);
		    if (!begin) {
			result += ", ";
		    } else {
			begin = false;
		    }
		    result += "sort "+from.getName()+" to "+to.getName();
		}
		
	    }

	    result += ")";
	    
	    break;
	    
	default:
	    result += "???";
	}
	
	return result;
    }

    

    public boolean equals(Object object) 
    {
	if (!(object instanceof ModuleName)) {
	    return false;
	}

	ModuleName name = (ModuleName)object;

	if (name.op == this.op) {
	    switch (op) {
	    case ATOM:
		if (name.atom.equals(this.atom)) {
		    return true;
	        } 
		break;
	    case ANNOTATE:
		
		if (name.atom.equals(this.atom)  &&
		    subexps.get(0).equals(name.subexps.get(0))) {
		    return true;
	        }     
		break;
	    case SUM:
		if (subexps.get(0).equals(name.subexps.get(0)) &&
		    subexps.get(1).equals(name.subexps.get(1))) {
		    return true;
	        }     
		break;
	    case INSTANCE:
		if (name.subexps.size() == this.subexps.size()) {
		    for (int i=0; i<subexps.size(); i++) {
			if (!name.subexps.get(i).equals(subexps.get(i))) {
			    return false;
			}
		    }
	            return true;
		} else {
		    return false;
		}
	    case GENERAL_INSTANCE:
		
		if (name.subexps.size() == this.subexps.size()) {
		    for (int i=0; i<subexps.size(); i++) {
			Object obj1 = this.subexps.get(i);
			Object obj2 = name.subexps.get(i);
			
			if (obj1 instanceof View &&
			    obj2 instanceof View) {

			    View v1 = (View)obj1;
			    View v2 = (View)obj2;

			    if (v1.name != null && v2.name != null && 
				!v1.name.equals(v2.name)) {
				return false;
			    }
			} else if (obj1 instanceof ModuleName &&
			    obj2 instanceof ModuleName) {

			    ModuleName m1 = (ModuleName)obj1;
			    ModuleName m2 = (ModuleName)obj2;
			    
			    if (!m1.equals(m2)) {
				return false;
			    }
			} else if (obj1 instanceof ModuleName &&
				   obj2 instanceof View) {

			    View v2 = (View)obj2;
			    ModuleName m1 = (ModuleName)obj1;

			    if (!v2.name.equals(m1.toString())) {
				return false;
			    }
			    
			} else if (obj2 instanceof ModuleName &&
				   obj1 instanceof View) {

			    View v1 = (View)obj1;
			    ModuleName m2 = (ModuleName)obj2;

			    if (!v1.name.equals(m2.toString())) {
				return false;
			    }			    			    
			} else {
			    return false;
			}

			/*
			if (!name.subexps.get(i).equals(subexps.get(i))) {
			    return false;
			}
			*/
		    }
	            return true;
		} else {
		    return false;
		}		
	    case RENAMING:

		if (subexps.get(0).equals(name.subexps.get(0))) {

		    Map map1 = (Map)this.subexps.get(1);
		    Map map2 = (Map)name.subexps.get(1);

		    if (map1.size() != map2.size()) {
			return false;
		    }
		    		    
		    Iterator itor = map1.keySet().iterator();
		    while (itor.hasNext()) {
			Object obj = itor.next();
			if (obj instanceof Sort) {
			   Sort from = (Sort)obj;
			   Sort to = (Sort)map1.get(from);

			   boolean found = false;
			   Iterator itor2 = map2.keySet().iterator();
			   while (itor2.hasNext()) {
			       Object obj2 = itor2.next();
			       if (from.equals(obj2)) {
				  Sort sort = (Sort)map2.get(obj2);
				  if (sort.equals(to)) {
				      found = true;
				      break;
				  }
			       }
			   }

			   if (!found) return false;
			   			   
			} else {
			    
			   Operation from = (Operation)obj;
			   Operation to = (Operation)map1.get(from);

			   boolean found = false;
			   Iterator itor2 = map2.keySet().iterator();
			   while (itor2.hasNext()) {
			       Object obj2 = itor2.next();
			       if (from.equals(obj2)) {
				  Operation op = (Operation)map2.get(obj2);
				  if (op.equals(to)) {
				      found = true;
				      break;
				  }
			       }
			   }

			   if (!found) return false;
			   
			}
		    }
		    return true;
		    
		} else {
		    return false;
		}
		
	    default:
	    }
	    
	}

	return false;
 
    }

    public ModuleName changeAbsoluteModuleName(ModuleName from, ModuleName to) 
    {
 	
	if (this.equals(from)) {
	    return to;
	} else {
	    return this;
	}
    }
    

    public ModuleName changeModuleName(ModuleName from, ModuleName to) 
    {
 	
	if (this.equals(from)) {
	    return to;
	}
	
	switch (this.op) {
	case ATOM:
	    return this;
	case ANNOTATE:
	    
	    ModuleName m = (ModuleName)subexps.get(0);
	    m = m.changeModuleName(from, to);
	    m = m.addAnnotation(atom);
	    return m;
	    	    
	case SUM:

	    ModuleName m1 = (ModuleName)subexps.get(0);
	    m1 = m1.changeModuleName(from, to);
	    
	    ModuleName m2 = (ModuleName)subexps.get(1);
	    m2 = m2.changeModuleName(from, to);
	    
	    return m1.sum(m2);
	    
	case INSTANCE:
	    
	    return this;
	    
	case GENERAL_INSTANCE :
	    
	    ModuleName m0 = (ModuleName)subexps.get(0);
	    m0 = m0.changeModuleName(from, to);
	    
	    List list = new ArrayList();
	    for (int i=1; i<subexps.size(); i++) {
		Object obj = subexps.get(i);
		if (obj instanceof ModuleName) {
		    ModuleName tmp = (ModuleName)obj;
		    tmp = tmp.changeModuleName(from, to);
		    list.add(tmp);
		} else {
		    
		    View view = (View)obj;
		    if (view.target.modName.toString().equals(view.name)) {

			ModuleName tmp = view.target.modName;
			
			if (to.view != null &&
			    to.view.source.modName.equals(tmp)) {

			    list.add(to.view);
			    continue;
			    
                        } else {
			    tmp = tmp.changeModuleName(from, to);
			    view = view.copy(tmp.toString());
			    list.add(view);
			    continue;
			}
			
		    }
		    		    
		    list.add(obj);
		}
	    }

	    return m0.instance(list);
	    
	case RENAMING:

	    m0 = (ModuleName)subexps.get(0);
	    m0 = m0.changeModuleName(from, to);
	    Map map = (Map)subexps.get(1);
 
	    return m0.renaming(map);
	    	    
	default:
	    return this;
	    
	}
		
    }



    public ModuleName changeParameterName(String from, String to) 
    {
 		
	switch (this.op) {
	case ATOM:
	    return this;
	case ANNOTATE:

	    ModuleName m = (ModuleName)subexps.get(0);
	    if (atom.equals(from)) {
		return m.addAnnotation(to);
	    } else {
		m = m.changeParameterName(from, to);
		m = m.addAnnotation(atom);
		return m;
	    }
	    
	case SUM:

	    ModuleName m1 = (ModuleName)subexps.get(0);
	    m1 = m1.changeParameterName(from, to);
	    
	    ModuleName m2 = (ModuleName)subexps.get(1);
	    m2 = m2.changeParameterName(from, to);
	    
	    return m1.sum(m2);
	    
	case INSTANCE:
	    
	    return this;
	    
	case GENERAL_INSTANCE :
	    
	    ModuleName m0 = (ModuleName)subexps.get(0);
	    m0 = m0.changeParameterName(from, to);
	    
	    List list = new ArrayList();
	    for (int i=1; i<subexps.size(); i++) {
		Object obj = subexps.get(i); 
		if (obj instanceof ModuleName) {
		    ModuleName tmp = (ModuleName)obj;
		    tmp = tmp.changeParameterName(from, to);
		    list.add(tmp);
                } else if (obj instanceof View) {

		    list.add(obj);

		    /*
		    View view = (View)obj;
		    if (view.name.equals(view.target.modName.toString())) {
			view = view.copy(
			    view.target.modName.changeParameterName(from, to).toString());
                        list.add(view);
		    } else {
			list.add(obj);
		    }
		    */
		    // end modification

		} else {
		    list.add(obj);
		}
	    }

	    return m0.instance(list);
	    
	case RENAMING:

	    m0 = (ModuleName)subexps.get(0);
	    m0 = m0.changeParameterName(from, to);
	    Map map = (Map)subexps.get(1);
 
	    return m0.renaming(map);
	    	    
	default:
	    return this;
	    
	}
		
    }
    
    public boolean containsToken(String string) 
    {
	switch (op) {
	case ATOM:
	    return atom.equals(string);
	case ANNOTATE:
	    return atom.equals(string) || subexps.get(0).equals(string);
	case SUM:
	    ModuleName m1 = (ModuleName)subexps.get(0);	    
	    ModuleName m2 = (ModuleName)subexps.get(1);
	    return m1.containsToken(string) || m2.containsToken(string);
	case INSTANCE:
	    m1 = (ModuleName)subexps.get(0);
	    if (m1.containsToken(string)) {
		return true;
	    }
	    return false;
	case GENERAL_INSTANCE :
	    m1 = (ModuleName)subexps.get(0);
	    if (m1.containsToken(string)) {
		return true;
	    }
	    return false;
	case RENAMING:
	    return false;
	default:
	    return false;
	}
		
    }
    
    
}





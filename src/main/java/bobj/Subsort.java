
package bobj;

import java.util.*;
import java.io.*;

public class Subsort  implements Serializable {

    protected Hashtable subsorts = new Hashtable();

    public void addSubsort(Sort parent, Sort child)
	throws SubsortException {

	// first get all subsorts for parent and child

	Vector pv = new Vector();
	Vector cv = new Vector();

	boolean p = false;
	boolean c = false;

	Enumeration e = subsorts.keys();
	while (e.hasMoreElements() && (!p || !c)) {
	    Sort sort = (Sort)e.nextElement();
	    if (sort.equals(parent)) {
		pv = (Vector)subsorts.get(sort);
		subsorts.remove(sort);
		p = true;
	    } else if (sort.equals(child)) {
		cv = (Vector)subsorts.get(sort);
		subsorts.remove(sort);
		c = true;
	    }
	}

	// insert child into pv

	e = pv.elements();
	boolean found = false;
	while (e.hasMoreElements() && !found) {
	    Sort sort = (Sort)e.nextElement();
	    if (sort.equals(child)) {
		found = true;
	    }
	}

	if (!found) pv.addElement(child);

	// insert all the elements of cv into pv

	Enumeration ee = cv.elements();
	while (ee.hasMoreElements()) {

	    Sort tmp = (Sort)ee.nextElement();
	    if (tmp.equals(parent)) {
		throw new SubsortException("contradiction subsort: "+
					   tmp.getName()+
					   " and "+parent.getName());
	    }

	    e = pv.elements();
	    found = false;
	    while (e.hasMoreElements() && !found) {
		Sort sort = (Sort)e.nextElement();
		if (sort.equals(tmp)) {
		    found = true;
		}
	    }
	    if (!found) pv.addElement(tmp);

	}

	subsorts.put(parent,pv);
	subsorts.put(child,cv);

	// insert child and all the elements in cv to all possible places
	ee = subsorts.keys();
	while (ee.hasMoreElements()) {
	    Sort sort = (Sort)ee.nextElement();
	    Vector sv = (Vector)subsorts.get(sort);

	    // if sv contains parent, then insert 
	    boolean has = has(sv, parent);
	    if (has) {
		insert(sv, child);
		for (int i=0; i<cv.size(); i++) {
		    Sort tmp = (Sort)cv.elementAt(i);
		    insert(sv, tmp);
		}
	    }
	}

	
    }


    private static void insert(Vector set, Sort sort) {
	for (int i=0; i<set.size(); i++) {
	    Sort tmp = (Sort)set.elementAt(i);
	    if (tmp.equals(sort)) {
		return;
	    }
	}
	set.addElement(sort);
    }


    private static boolean has(Vector set, Sort sort) {

	for (int i=0; i<set.size(); i++) {
	    Sort tmp = (Sort)set.elementAt(i);
	    if (tmp != null && tmp.equals(sort)) {
		return true;
	    }
	}
	return false;
    }


    public boolean isSubsort(Sort parent, Sort child) {
       
       
	boolean result = false;

	if (parent.getName().equals("Universal") &&
	    parent.getInfo().equals("system-default")) {
	    result = true;
	} else {

	    Enumeration e = subsorts.keys();
	    Sort sort = null;

	    while (e.hasMoreElements() && !result) {
		sort = (Sort)e.nextElement();
		if (sort.equals(parent)) {
		    result = true;
		}
	    }
	  
	    if (result) {
		Vector v = (Vector)subsorts.get(sort);
		result = false;

		e = v.elements();
		while (e.hasMoreElements() && !result) {
		    sort = (Sort)e.nextElement();
		    if (sort.equals(child)) {
			result = true;
		    }           
		}
	    }
	}

	return result;

    }


    public String toString() {

	String result = "";
	Enumeration e = this.subsorts.keys();
	while (e.hasMoreElements()) {
	    Sort parent = (Sort)e.nextElement();
	    Vector v = (Vector)this.subsorts.get(parent);

	    if (v != null && v.size() != 0) {
		result += "  subsorts ";
		for (int i=0; i<v.size(); i++) {
		    Sort kid = (Sort)v.elementAt(i);
		    result += kid.getName()+"."+kid.getModuleName()+" ";
		}
		result += "< "+parent.getName()+" .\n";
	    }
	}

	return result;
    }



    public Sort[] getChildren(Sort parent) {

	Vector kids = new Vector();
	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    Sort sort = (Sort)e.nextElement();
	    if (sort.equals(parent)) {
		kids = (Vector)subsorts.get(sort); 
	    }
	}

	Sort[] result = new Sort[kids.size()];
	kids.copyInto(result);
	return result;
    }

    
    protected Subsort changeModuleName(ModuleName olds, ModuleName news) {
	
	Subsort result = new Subsort();

	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    
	    Sort ps = (Sort)e.nextElement();
	    Vector vec = (Vector)subsorts.get(ps);
	    
	    ps = ps.changeModuleName(olds, news);
	   
	    Vector res = new Vector();
	    if (vec != null) {
		for (int i=0; i<vec.size(); i++) {
		    Sort tmp = (Sort)vec.elementAt(i);		
		    tmp = tmp.changeModuleName(olds, news);
		    res.addElement(tmp);
		}
	    }

	    result.subsorts.put(ps, res);

	}

	return result;

    }


    protected Subsort changeAbsoluteModuleName(ModuleName olds,
					       ModuleName news) {
	
	Subsort result = new Subsort();

	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    
	    Sort ps = (Sort)e.nextElement();
	    Vector vec = (Vector)subsorts.get(ps);
	    
	    ps = ps.changeAbsoluteModuleName(olds, news);
	   
	    Vector res = new Vector();
	    if (vec != null) {
		for (int i=0; i<vec.size(); i++) {
		    Sort tmp = (Sort)vec.elementAt(i);		
		    tmp = tmp.changeAbsoluteModuleName(olds, news);
		    res.addElement(tmp);
		}
	    }

	    result.subsorts.put(ps, res);

	}

	return result;

    }


    protected Subsort changeParameterName(String olds, String news) {
	
	Subsort result = new Subsort();

	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    
	    Sort ps = (Sort)e.nextElement();
	    Vector vec = (Vector)subsorts.get(ps);
	    
	    ps = ps.changeParameterName(olds, news);
	   
	    Vector res = new Vector();
	    if (vec != null) {
		for (int i=0; i<vec.size(); i++) {
		    Sort tmp = (Sort)vec.elementAt(i);		
		    tmp = tmp.changeParameterName(olds, news);
		    res.addElement(tmp);
		}
	    }

	    result.subsorts.put(ps, res);

	}

	return result;

    }

    
    protected Subsort changeSort(Sort olds, Sort news) {

        	
	Subsort tmp = new Subsort();
	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    Sort parent = (Sort)e.nextElement();
	    Vector cv = (Vector)subsorts.get(parent);

	    if (parent.equals(olds)) {
		parent = news;
	    }

	    for (int i=0; i<cv.size(); i++) {
		Sort child  = (Sort)cv.elementAt(i);
		if (child.equals(olds)) {
		    child = news;
		}
		try {
		    tmp.addSubsort(parent, child);
		} catch (Exception ex) {}
	    }

	}

	return tmp;
	
    }
    

    protected Subsort addAnnotation(String name, Map env) {

	Subsort result = new Subsort();

	Enumeration e = this.subsorts.keys();
	while (e.hasMoreElements()) {

	    Sort ps = (Sort)e.nextElement();
	    Vector vec = (Vector)subsorts.get(ps);
	    Sort sort = ps.addAnnotation(name, env);

	    for (int i=0; i<vec.size(); i++) {
		Sort tmp = (Sort)vec.elementAt(i);
                tmp = tmp.addAnnotation(name, env);
		try {
		    result.addSubsort(sort, tmp);
		} catch (Exception ex){
		}
	    }

	}

	return result;

    }


    protected Subsort removeAnnotation(String name) {

	Subsort result = new Subsort();

	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    
	    Sort ps = (Sort)e.nextElement();
	    Vector vec = (Vector)subsorts.get(ps);
	    Vector res = new Vector();
	    	    
	    for (int i=0; i<vec.size(); i++) {
		Sort tmp = (Sort)vec.elementAt(i);
                tmp = tmp.removeAnnotation(name);
		res.addElement(tmp);
		
	    }
	    ps = ps.removeAnnotation(name);
	    result.subsorts.put(ps, res);

	}

	return result;

    }



    public boolean contains(Subsort ss) {
	boolean result = true;

	Enumeration e = ss.subsorts.keys();
	while (e.hasMoreElements()) {
	    Sort parent = (Sort)e.nextElement();
	    Vector v = (Vector)ss.subsorts.get(parent);
	    for (int i=0; i<v.size(); i++) {
		Sort kid = (Sort)v.elementAt(i);
		result = isSubsort(parent, kid);
		if (!result)  return false;
	    }
	}

	return result;
    }


    public Sort canApply(Sort s1, Sort s2) {

	Sort result = null;

	Vector kids = null;
	Enumeration e = subsorts.keys();
	while (e.hasMoreElements()) {
	    Sort tmp = (Sort)e.nextElement();
	    if (s2.equals(tmp)) {
		kids = (Vector)subsorts.get(tmp);
		break;
	    }
	}

	if (kids != null) {
	    for (int i=0; i<kids.size(); i++) {
		Sort tmp = (Sort)kids.elementAt(i);
		if (isSubsort(s1, tmp)) {
		    return tmp;
		}
	    }
	}

	return result;
    }


    public Object clone() {
	Subsort result = new Subsort();
	Enumeration enum_ = this.subsorts.keys();
	while (enum_.hasMoreElements()) {
	    Sort sort = (Sort)enum_.nextElement();
	    Vector vec = (Vector)this.subsorts.get(sort);
	    vec = (Vector)vec.clone();
	    result.subsorts.put(sort, vec);
	}
	
	//result.subsorts = (Hashtable)subsorts.clone();
	return result;
    }



    
    
}














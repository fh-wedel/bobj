
package bobj;

/**
 * a class representing variable in the first order term.
 *
 * @author  Kai Lin
 * @version %I% %G%
 * @see Sort
 *
 */

import java.io.*;
import java.util.*;

public class Variable implements Serializable{

    protected String name;
    protected Sort sort;
    protected String info;


    /**
     * create a variable by the specified string 
     * and sort without information.
     *
     * @param v variable name
     * @param s sort
     * @return a variable with the specified string and sort.
     */

    public Variable(String name, Sort sort) {
	this.name = name.trim();
	this.sort = sort;
	this.info = "no information available.";
    }


    /**
     * create a variable by the specified string and sort and information.
     *
     * @param v variable name
     * @param s sort
     * @param i information string
     * @return a variable with the specified string and 
     *         sort and information.
     */
    public Variable(String name, Sort sort, String info) {
	this.name = name.trim();
	this.sort = sort;
	this.info = info;
    }

    /**
     * return the name of this variable.
     *
     */
    public String getName() {
	return name;
    }


    /**
     * return the sort of this variable. 
     *
     */
    public Sort getSort() {
	return sort;
    }


    /**
     * return the sort name of this variable. 
     *
     */
    public String getSortName() {
	return sort.getName();
    }

    /**
     * return the information of this variable. 
     *
     */

    public String getInfo() {
	return info;
    }

    /**
     * return a string representingthis variable, and it has the
     * form as "var N : Nat".
     *
     */
    public String toString() {
	return  "var "+name+" : "+sort.getName()+"."+sort.getModuleName();     
    }


    public boolean equals(Object obj) {
	if (obj instanceof Variable) {
	    Variable var = (Variable)obj;
	    return  this.name.equals(var.name) && this.sort.equals(var.sort) ;
	}

	return false;
    }

 
    protected Variable changeSort(Sort olds, Sort news) 
    {
        if (this.sort.equals(olds)) {
	    Variable var = new Variable(name, news);
	    var.info = info;
	    return var;
	} else {
	    return this;
	}
	
    }

    
    protected Variable changeSortTo(Sort sort) 
    {
	Variable var = new Variable(name, sort);
	var.info = info;
	return var;
    }
    

    public Variable changeModuleName(ModuleName olds, ModuleName news) {

	Variable var = new Variable(name, sort.changeModuleName(olds, news));
	var.info = info;
	return var;	
	
    }

    public Variable changeAbsoluteModuleName(ModuleName olds,
					     ModuleName news) {

	Variable var = new Variable(name,
				    sort.changeAbsoluteModuleName(olds, news));
	var.info = info;
	return var;	
	
    }


    public Variable changeParameterName(String olds, String news) {

	Variable var = new Variable(name,
				    sort.changeParameterName(olds, news));
	var.info = info;
	return var;	
	
    }
    
    public Variable addAnnotation(String name, Map env) {
	Variable var = new Variable(this.name, sort.addAnnotation(name, env));
	var.info = info;
	return var;	
    }

    public Variable removeAnnotation(String name) {
	Variable var = new Variable(this.name, sort.removeAnnotation(name));
	var.info = info;
	return var;	
    }
}




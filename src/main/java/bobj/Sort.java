
package bobj;

import java.util.Map;
import java.util.HashMap;
import java.io.Serializable;

/**
 * The class Sort implements the sort in the first order algebra.
 *
 * @author Kai Lin
 * @version %I% %G%
 *
 */

public class Sort implements Serializable {

    /**
     *  Indicates the name of this sort.
     */
    private String name;

    /**
     * Indicates the associated information. 
     */
    private ModuleName mod;

    /**
     * properties. 
     */
    protected Map props;

    
    
    /**
     * Constructs a new visible sort by using the specified string as name
     * and using the specified module name.
     *
     * @param      name string
     * @param      mod module name
     * @return     sort using the specified strings as name and information.
     */
    public Sort(String name, ModuleName mod)
    {    
	this.name = name;
        this.mod = mod;
        this.props = new HashMap();
	this.props.put("info", "no information available.");
    }

    /**
     * Returns the name of this sort. 
     *
     */
    public String getName() {
	return name;
    }

    /**
     * Returns the module name of this sort. 
     *
     */
    public ModuleName getModuleName() {
	return mod;
    }


    /**
     * Returns the information of this sort. 
     *
     */
    public String getInfo() {
	return (String)this.props.get("info");
    }


    /**
     * Set the infomation  as the specified string.
     *
     */
    public void setInfo(String info) {
	this.props.put("info", info);
    }

    /*
     * set a property with the specified name 
     */
    public void setProperty(String name, Object object)
    {
        props.put(name, object);
    }

    /*
     * get a property with the specified name
     */
    public Object getProperty(String name)
    {
        return props.get(name);
    }


    /*
     * check whether this sort is initial sort
     */
    public boolean isInitial()
    {
        return false;
    }

    /*
     * check whether this sort is hidden sort
     */
    public boolean isHidden()
    {
        return false;
    }

    /**
     * chech whether two sorts are equals
     */
    public boolean equals(Object object)
    {
	
        if (object instanceof Sort) {
            Sort sort = (Sort)object;
            if (sort.name.equals(name)) {
		if (sort.mod != null && mod != null && sort.mod.equals(mod)) {
		    return true;
		} else if (sort.mod == null && mod == null ) {
		    return true;
		} else {
		    return false;
		}
		
            } else {
                return false;
            }
        }
        return false;
    }


    public int hashCode() {
	return name.hashCode()+mod.hashCode();
    }


    /**
     * Modiies the sort name.
     *
     * @param s a string used as a new name
     *
     */
    protected void setName(String name) {
	this.name = name;
    }

    /**
     * Returns a string representation of this sort, and it has the
     * form as "sort Nat".
     *
     */
    public String toString() {
	if (mod == null) {
	    return "sort "+name;
	} else {
	    return "sort "+name+"."+mod;
	}
    }


    /**
     * check whether this sort is system default sort
     */
    protected boolean isDefault() {
	return props.get("info").equals("system-default");
    }


    protected Sort addAnnotation(String name, Map env) {
	if (!isDefault()) {

	    Integer aInt = (Integer)env.get(mod);
	    
	    if (aInt != null && aInt.intValue() == 0) {
		return this;
	    }
	    	       
	    if (mod.hasNotation()) {
		return this;
	    }

	    if (this.isInitial()) {
		return this;
	    }
	    
	    Sort sort = new Sort(this.name, mod.addAnnotation(name));
	    sort.props = this.props;
	    return sort;
	    
	} else {
	    return this;
	}
    }


    protected Sort removeAnnotation(String name) {
	if (mod.hasNotation(name)) {
	    Sort sort = new Sort(this.name, mod.getOriginModuleName());
	    sort.props = this.props;
	    return sort;
        } else {
	    return this;
	}
    }


    public Sort changeModuleName(ModuleName olds, ModuleName news) 
    {
	
	Sort sort = new Sort(name, mod.changeModuleName(olds, news));
	sort.props = this.props;
	return sort;	
	
    }
        
    public Sort changeAbsoluteModuleName(ModuleName olds, ModuleName news) 
    {
	
	Sort sort = new Sort(name, mod.changeAbsoluteModuleName(olds, news));
	sort.props = this.props;
	return sort;	
	
    }


   public Sort changeParameterName(String from, String to) 
    {
	
	Sort sort = new Sort(name, mod.changeParameterName(from, to));
	sort.props = this.props;
	return sort;	
	
    }
    
}





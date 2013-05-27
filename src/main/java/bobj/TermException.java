
package bobj;

public class TermException extends Exception {
    
    int count;
    
    public TermException() {
	super();
    }

    public TermException(String msg) {
	super(msg);
    }

         
    public TermException(String msg, int count) 
    {
	super(msg);
	this.count = count;
    }

    
    public int getCount() 
    {
	return this.count;
    }

}

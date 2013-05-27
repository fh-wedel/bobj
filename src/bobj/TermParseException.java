
package bobj;

public class TermParseException extends Exception 
{
    int count;

    public TermParseException(String msg) 
    {
	super(msg);
    }
    
    public TermParseException(String msg, int count) 
    {
	super(msg);
	this.count = count;
    }
    
    public int getCount() 
    {
	return this.count;
    }
    
}

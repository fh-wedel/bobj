
package bobj;

import java.util.*;

class TermSelection 
{

    final static public int RANGE = 0;
    final static public int SEQ = 1;
    final static public int TOP = 2;
    final static public int WITHIN = 3;
    final static public int SUB = 4;

    protected int kind;
    protected int begin, end;
    protected int[] seq;
    protected TermSelection next;    
    
    public TermSelection(int begin, int end) 
    {
	if (begin == -1 && end == -1) {
	    this.kind = TOP;
	} else {
	    this.kind = RANGE;
	    this.begin = begin;
	    this.end = end;
	}
	
    }

    
    public TermSelection(boolean at) 
    {
	if (at) {
	    this.kind = TOP;
	} else {
	    this.kind = WITHIN;
	}
    }

    
    public TermSelection(int[] seq) 
    {
	this.kind = SEQ;
	this.seq = seq;
    }


    public TermSelection(ArrayList list) {
	this.kind = SUB;
	this.seq = new int[list.size()];
	for (int i=0; i<list.size(); i++) {
	    Integer aInt = (Integer)list.get(i);
	    this.seq[i] = aInt.intValue();
	}
    }

    public void append(TermSelection select) 
    {
	if (this.kind == WITHIN || this.next != null) {
	    throw new Error("oops111");
	}
	
	if (this.kind == TOP) {
	    this.kind = select.kind;
	    this.begin = select.begin;
	    this.end = select.end;
	    this.seq = select.seq;
	    this.next = select.next;
	} else if (select.kind == TOP) {
	    
	} else {
	    this.next = select;
	}
	
    }
    
    
    public String toString() 
    {

	String result = "";
	if (next != null) {
	    result = next.toString()+" of ";
	}
	
	switch(kind) {
	case RANGE:
	    if (begin < end) {
		return result+"["+begin+".."+end+"]";		
	    } else {
		return result+"["+begin+"]";
	    }
	case SEQ:
	    String res = "(";
	    for (int i=0; i<seq.length; i++) {
		res += seq[i]+" ";
	    }
	    return result+res.trim()+")";
        case SUB:
	    res = "{";
	    for (int i=0; i<seq.length; i++) {
		if (i == seq.length -1) {
		    res += (seq[i]+1);
		} else {
		    res += (seq[i]+1)+",";
		}
	    }
	    return result+res.trim()+"}";	    
	case TOP:
	    return "top";
        case WITHIN:
	    return "within term";
	default:
	    return "wrong";
	}
	
    }
    
	
}

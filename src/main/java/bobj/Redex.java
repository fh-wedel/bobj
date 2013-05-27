
package bobj;

class Redex {

    Term point;
    Term term;
    Term next;
    Equation eq;
    int position;

    public Redex(Term point, Term term) {
	this.point = point;
	this.term = term;
	this.position = -1;
    }

    public Redex(Term point, Term term, Equation eq) {
	this.point = point;
	this.term = term;
	this.position = -1;
	this.eq = eq;
    }

    public Term getPoint() {
	return point;
    }

    public Term getTerm() {
	return term;
    }

    public String toString() 
    {
	String result = "";
	result += "term = "+term+"\n";
        result += "point = "+point+"\n";
	result += "next = "+next+"\n";
	result += "eq "+eq+"\n";
	return result;
	
    }
    
} 


package bobj;

class FloatModule 
{
    static Module floatt = ModuleFactory.createFloat();

    static Sort boolSort = (Sort)floatt.sorts.elementAt(0);
    static Sort floatSort = (Sort)floatt.sorts.elementAt(2);

    static Operation add = (Operation)floatt.operations.elementAt(10);
    static Operation sub = (Operation)floatt.operations.elementAt(11);
    static Operation mult = (Operation)floatt.operations.elementAt(12);
    static Operation div = (Operation)floatt.operations.elementAt(13);
    static Operation le = (Operation)floatt.operations.elementAt(14);
    static Operation leq = (Operation)floatt.operations.elementAt(15);
    static Operation gt = (Operation)floatt.operations.elementAt(16);
    static Operation gte = (Operation)floatt.operations.elementAt(17);
    static Operation exp = (Operation)floatt.operations.elementAt(18);
    static Operation log = (Operation)floatt.operations.elementAt(19);
    static Operation sqrt = (Operation)floatt.operations.elementAt(20);
    static Operation abs = (Operation)floatt.operations.elementAt(21);
    static Operation sin = (Operation)floatt.operations.elementAt(22);
    static Operation cos = (Operation)floatt.operations.elementAt(23);
    static Operation atan = (Operation)floatt.operations.elementAt(24);
    static Operation pi = (Operation)floatt.operations.elementAt(25);

    public static void main(String args[]){
	System.out.println("pt = "+pi);
	System.out.println("log = "+log);
	System.out.println("gt = "+gt);
	System.out.println("div = "+div);
    }
    
 
}

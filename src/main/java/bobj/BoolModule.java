
package bobj;

public class BoolModule 
{
    public static Module bool = ModuleFactory.createBool();
    public static Sort boolSort = (Sort)bool.sorts.elementAt(0);
    public static Sort univSort = (Sort)bool.sorts.elementAt(1);
    public static Operation trueOp = (Operation)bool.operations.elementAt(0);
    public static Operation falseOp = (Operation)bool.operations.elementAt(1);
    public static Operation metaEq = (Operation)bool.operations.elementAt(2);
    public static Operation metaNeq = (Operation)bool.operations.elementAt(3);
    public static Operation metaIf = (Operation)bool.operations.elementAt(4);
    public static Operation and = (Operation)bool.operations.elementAt(5) ;
    public static Operation or = (Operation)bool.operations.elementAt(6);    
    public static Operation not = (Operation)bool.operations.elementAt(9);
    
}

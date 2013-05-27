
package bobj;

class IntModule 
{
    static Module imt = ModuleFactory.createInt();

    static Sort boolSort = (Sort)imt.sorts.elementAt(0);
    static Sort intSort = (Sort)imt.sorts.elementAt(2);
    static Sort nzintSort = (Sort)imt.sorts.elementAt(3);	
    static Sort natSort = (Sort)imt.sorts.elementAt(4);
    static Sort zeroSort = (Sort)imt.sorts.elementAt(5);
    static Sort nznatSort = (Sort)imt.sorts.elementAt(6);

    static Operation trueOp = (Operation)imt.operations.elementAt(0);
    static Operation falseOp = (Operation)imt.operations.elementAt(1);
    static Operation zeroOp = (Operation)imt.operations.elementAt(12);

}

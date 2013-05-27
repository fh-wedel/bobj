
package bobj;

public class BOBJModule {

    public static ModuleName getModuleName() {
	return new ModuleName("BOBJ");
    }


    public static Operation getSetsortOperation() {
	try {
	    Sort[] args = { BoolModule.univSort, BoolModule.univSort };
	    Sort res = BoolModule.univSort;
	    Operation op = new Operation("~setsort~",
					 args,
					 res,
					 getModuleName());
	    op.info = "system-default";
	    return op;
	} catch (Exception e) {
	    return null;
	}
    }


    public static Operation getSortOperation() {
	try {
	    Sort[] args = { BoolModule.univSort };
	    Sort res = QidlModule.idSort;
	    Operation op = new Operation("~sort~",
					 args,
					 res,
					 getModuleName());
	    op.info = "system-default";
	    return op;
	} catch (Exception e) {
	    return null;
	}
    }


    public static Operation getFinalSortOperation() {
	try {
	    Sort[] args = { BoolModule.univSort };
	    Sort res = QidlModule.idSort;
	    Operation op = new Operation("~sort*~",
					 args,
					 res,
					 getModuleName());
	    op.info = "system-default";
	    return op;
	} catch (Exception e) {
	    return null;
	}
    }
    
    
}

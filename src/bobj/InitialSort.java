
package bobj;

public class InitialSort extends Sort
{

    public InitialSort(Sort sort) {
	super(sort.getName(), sort.getModuleName());
	props = sort.props;
    }

    public InitialSort(String name, ModuleName mod)
    {
        super(name, mod);
    }

    public boolean isInitial()
    {
        return true;
    }


    public Sort changeModuleName(ModuleName olds, ModuleName news) 
    {

	Sort sort = new InitialSort(getName(),
				    getModuleName().changeModuleName(olds,
								     news));
	sort.props = this.props;
	return sort;	
	
    }

    public Sort changeAbsoluteModuleName(ModuleName olds, ModuleName news) 
    {
	
	Sort sort = new InitialSort(getName(), 
				    getModuleName().changeAbsoluteModuleName(olds, news));
	sort.props = this.props;
	return sort;	
	
    }

    public Sort changeParameterName(String from, String to) 
    {
	
	Sort sort = new InitialSort(getName(),
			   getModuleName().changeParameterName(from, to));
	sort.props = this.props;
	return sort;	
    }

}





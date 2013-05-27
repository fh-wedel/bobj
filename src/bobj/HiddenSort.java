
package bobj;

public class HiddenSort extends Sort
{

    public HiddenSort(Sort sort) {
	super(sort.getName(), sort.getModuleName());
	props = sort.props;
    }

    public HiddenSort(String name, ModuleName mod)
    {
        super(name, mod);
    }

    public boolean isHidden()
    {
        return true;
    }

    public Sort changeModuleName(ModuleName olds, ModuleName news) 
    {
	
	Sort sort = new HiddenSort(getName(),
				   getModuleName().changeModuleName(olds,
								    news));
	sort.props = this.props;
	return sort;	
	
    }    


    public Sort changeAbsoluteModuleName(ModuleName olds, ModuleName news) 
    {
	
	Sort sort = new HiddenSort(getName(), 
		      getModuleName().changeAbsoluteModuleName(olds, news));
	sort.props = this.props;
	return sort;	
	
    }

    public Sort changeParameterName(String from, String to) 
    {
	
	Sort sort = new HiddenSort(getName(),
			   getModuleName().changeParameterName(from, to));
	sort.props = this.props;
	return sort;	
	
    }

}




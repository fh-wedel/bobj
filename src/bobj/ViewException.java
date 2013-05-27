
package bobj;

public class ViewException extends Exception {

    View view;

    public ViewException() {
	super();
    }

    public ViewException(String st) {
	super(st);
    }

    public ViewException(String st, View view) {
	super(st);
	this.view = view;
    }

    public View getView() {
	return view;
    }

}

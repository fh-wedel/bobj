
package bobj;

import java.util.*;
import java.io.*;

public class FastTermParser {

    public static boolean debug = false;
    
    Signature sig;
    ArrayList tokens;
    int[] paratheses;
    ArrayList[][] tables;
    Operation[] operations;

    public FastTermParser(Signature sig, String string) {
		
	this.sig = sig;

	//initialize tokens
	this.tokens = new ArrayList();
	StringTokenizer st = new StringTokenizer(string);
	while (st.hasMoreTokens()) {
	    tokens.add(st.nextToken());
	}

	//set up parathesis counts
	paratheses = new int[tokens.size()];
	int count = 0;
	for (int i=0; i<tokens.size(); i++) {
	    String token = (String)tokens.get(i);
	    if (sig.balancedBrackets) {
		  if (token.equals("(") ||
		      token.equals("{") ||
		      token.equals("[")) {
		      paratheses[i] = count;
		      count++;
		  } else if (token.equals(")") ||
			     token.equals("}") ||
			     token.equals("]")) {
		      count--;
		      paratheses[i] = count;
		  } else {
		      paratheses[i] = count;
		  }
	    } else {
		  if (token.equals("(")) {
		      paratheses[i] = count;
		      count++;
		  } else if (token.equals(")")) {
		      count--;
		      paratheses[i] = count;
		  } else {
		      paratheses[i] = count;
		  }		
	    }

	}
	    
	//initialize tables
	tables = new ArrayList[tokens.size()][tokens.size()];

	// prepare operations
	Operation[] ops = sig.getOperations();
	Vector opList = new Vector(); 
	for (int i=0; i<ops.length; i++) {
	    Vector vec = ops[i].getTokens();
	    boolean hasLetter = false;
	    for (int j=0; j<vec.size(); j++) {
		Object obj = vec.elementAt(j);
		if (obj instanceof String) {
		    hasLetter = true;
		    if (tokens.contains(obj)) {

			// add ops[i] by the order
			int k;
			for (k=0; k<opList.size(); k++) {
			    Operation op = (Operation)opList.elementAt(k);
			    if (ops[i].less(sig, op)) {
				break;
			    }
			}

			if (k == opList.size()) {
			    opList.addElement(ops[i]);
			} else {
			    opList.insertElementAt(ops[i], k);
			}
			break;
		    }
		} 
	    }
	    if (!hasLetter) {
		opList.addElement(ops[i]);
	    }
	}
			
	operations = new Operation[opList.size()];
	opList.copyInto(operations);
    }


    
    public ArrayList parse() //throws TermParseException
    {
	
	for (int len=0; len<tokens.size(); len++) {
	    	    
	    for (int i=0; i+len<tokens.size(); i++) {

		/*
		System.out.println("\n----------------------");
		System.out.println("tokens = "+tokens+
				   "     size = "+tokens.size());
		System.out.println("begin = "+i+"   end = "+(i+len));
		*/
		
		// calculate tables[i, i+len]
                tables[i][i+len] = new ArrayList();

		// only handle balanced parenthese
		if (paratheses[i] != paratheses[i+len]) {
		    continue;
		}

		boolean o = true;
		for (int j=i+1; j<=len+i; j++) {
		    if (paratheses[j] < paratheses[i]) {
			o = false;
			break;
		    }
		}
		if (!o) {
		    continue;
		}

		
		// optimaization for the first token
	        String first = (String)tokens.get(i);
				
		if (!sig.firsts.contains(first)    && 
                    !first.startsWith("'")         &&
		    !first.startsWith("r:")        &&
		    !first.startsWith("~setsort~") && 
		    !first.startsWith("~sort~")    &&
		    !first.startsWith("~sort*~")) {
		    try {
			Integer.parseInt(first);
		    } catch (Exception e) {
			try {
			    Float.parseFloat(first);
			} catch (Exception ex) {
			    continue;
			}
		    }
		}		
				
		// optimaization for the last token
		
	        String last = (String)tokens.get(i+len);
		if (!sig.lasts.contains(last) && !last.startsWith("'")) {

		    boolean opt = true;
		    if (len > 0 ) {
			String last2 = (String)tokens.get(i+len-1);
			if (last2.equals(".")) {
			    opt = false;
			}
		    }

		    if (opt) {
			try {
			    Integer.parseInt(last);
			} catch (Exception e) {
			    try {
				Float.parseFloat(last);
			    } catch (Exception ex) {
				continue;
			    }
			}
		    }
		}    		

		// handle variable
		if (len == 0) {
		    String string = (String)tokens.get(i);
		    Variable[] vars = sig.getVariables();
		    for (int j=0; j<vars.length; j++) {
			if (vars[j].getName().equals(string)) {
			    add(tables[i][i], new Term(vars[j]));
			    break;
			}
		    }
		}

		// handle parentheses
		if (len > 1) {
		    
		    String l = (String)tokens.get(i);
		    String r = (String)tokens.get(i+len);
		    if (l.equals("(") && r.equals(")")) {
			addAllWithParenthese(tables[i][i+len],
					     tables[i+1][i+len-1]);
		    }
		}

		// handle build-in natural number
		ModuleName nat = new ModuleName("NZNAT");
		ModuleName imt = new ModuleName("INT");
		ModuleName floatt = FloatModule.floatt.getModuleName();
		
		Sort natSort = new Sort("NzNat",nat);
		Sort imtSort = new Sort("Int",imt);
		Sort floatSort = FloatModule.floatSort;
				
		if (len == 0 && sig.containsSystemSort(natSort)) {
		    String token = (String)tokens.get(i);
		    try {
			int num = Integer.parseInt(token);
			if (num > 0) {
			    try {
				Operation op = new Operation(token,
							     natSort,
							     nat);
				add(tables[i][i], new Term(op, new Term[0]));
			    } catch (Exception e) {}
			}
		    } catch (Exception ex){}
		}

		if (len == 0 && sig.containsSystemSort(imtSort)) {
		    String token = (String)tokens.get(i);
		    try {
			int num = Integer.parseInt(token);
			if (num < 0) {
			    try {
				Operation op = new Operation(token,
							     imtSort,
							     imt);
				add(tables[i][i], new Term(op, new Term[0]));
			    } catch (Exception e) {}
			}
		    } catch (Exception ex){}
		}

		if (len == 0 && sig.containsSystemSort(floatSort)) {
		    String token = (String)tokens.get(i);
		    
		    try {
			float num = Float.parseFloat(token);
			try {
			    Operation op = new Operation(token,
							 floatSort,
							 floatt);
			    add(tables[i][i], new Term(op, new Term[0]));
			} catch (Exception e) {
			}
		    } catch (Exception ex){}
		}
		
		// handle Id and its aliases
		if (len == 0) {
		    Sort[] sorts = sig.getQidAlias();
		    String token = (String)tokens.get(i);
		    if (sorts != null && sorts.length > 0 &&
			token.startsWith("'")) {
			for (int j=0; j<sorts.length; j++) {
			    try {
				Operation op =
				    new Operation(token, 
						  sorts[j], 
						  sorts[j].getModuleName());
				add(tables[i][i], new Term(op, new Term[0]));
			    } catch (Exception e){}
			}
		    }
		}

		// handle operation matching
		ArrayList ops = new ArrayList();
		ArrayList mts = new ArrayList();
		
		getAllTopMatches(i, i+len, ops, mts);
				
		for (int c=0; c<ops.size(); c++)  {
		    Operation op = (Operation)ops.get(c);
		    ArrayList list = (ArrayList)mts.get(c);
		    
		    if (list.size() == 0) {
			if (op.isConstant()) {
			    try {
				add(tables[i][i+len],
				    new Term(op, new Term[0]));
			    } catch (TermException e) {}
			}
		    } else {

			for (int j=0; j<list.size(); j++) {
			    
			    Match[] matches = (Match[])list.get(j);
			    ArrayList candidate = new ArrayList();
			    for (int k=0; k<matches.length; k++) {
				candidate.add(select(matches[k].x, 
						     matches[k].y, 
						     matches[k].sort));
				
			    }
			    
			    System.out.flush();
			    addAll(i,
				   i+len,
				   tables[i][i+len],
				   join(op, candidate));

			}
		    }
		}


		// handle module name
		if (len > 1) {
		    String dot = (String)tokens.get(i+len-1);
		    String s = (String)tokens.get(i+len);
		    
		    if (dot.equals(".")) {
			addByModuleName(tables[i][i+len],
					tables[i][i+len-2],
					new ModuleName(s));
		    }
		    
		}

		// handle complex module names
		if (len > 3) {

		    //System.out.println("===> "+tokens);
		    		    
		    String l = (String)tokens.get(i);
		    String r = (String)tokens.get(i+len);
		    if (!l.equals("(") && r.equals(")")) {
			int pos = i+len-1;
			int count = 1;
			while (count > 0 && pos >= i) {
			    String s = (String)tokens.get(pos);
			    if (s.equals("(")) {
				count--;
			    } else if (s.equals(")")) {
				count++;
			    }
			    pos--;
			}
						
			if (count == 0 && pos > i) {
			   String s = (String)tokens.get(pos);
			   if (s.equals(".")) {

			       String modexp = "";
			       for (int x=pos+2; x<i+len; x++) {
				  modexp += " "+tokens.get(x);
			       }

			       /*
			       System.out.println("===> "+modexp);

			       String mexp = "";
			       int y1 = modexp.indexOf("[");
			       int y2 = modexp.indexOf("]");
			       while (y1 != -1 || y2 != -1) {
				   if (y1 > y2 && y2 != -1) {
				       mexp += modexp.substring(0, y2-1);
				       mexp = mexp.trim();
				       mexp += " ] ";
				       modexp = modexp.substring(y2+1);
				   } else if (y2 > y1 && y1 != -1) {
				       mexp += modexp.substring(0, y1-1);
				       mexp = mexp.trim();
				       mexp += " ] ";
				       modexp = modexp.substring(y1+1);
				   } else if (y2 != -1 && y1 == -1) {
				       mexp += modexp.substring(0, y2-1);
				       mexp = mexp.trim();
				       mexp += " ] ";
				       mexp += modexp.substring(y2+1);
				   }
				   
			       }

			       System.out.println("mexp = "+mexp);
			       System.exit(0);
			       */
			       
			       StringReader in = new StringReader(modexp);
			       BOBJ bobj = new BOBJ(in);
			       bobj.modPool = BOBJ.client.modPool;
			       
			       try {   
				   Module mod = bobj.ModExpr((Module)sig);
				   addByModuleName(tables[i][i+len],
						   tables[i][pos-1],
						   mod.modName);

				   //Term tttt = (Term)tables[i][i+len].get(0);
				   //System.out.println(tttt.showStructureWithModuleName((Module)sig));
				   				   
			       } catch (Exception e) {
				   //e.printStackTrace();
			       }
			       				   
			       //System.exit(0);
			   }
			} 
			
		    }
                }
		
		
		// handle retraction
		if (len > 2) {
		    String string = (String)tokens.get(i);
		    int index = string.indexOf(">");
		    if (string.startsWith("r:") && index != -1) {
			String superSortName =
			    string.substring(0, index).substring(2).trim();
			String subSortName = string.substring(index+1).trim();
			
			Sort[] superSorts = sig.getSortsByName(superSortName);
			Sort[] subSorts = sig.getSortsByName(subSortName);

			if (superSorts.length == 1 &&
			    subSorts.length == 1 &&
			    sig.subsorts.isSubsort(superSorts[0],
						   subSorts[0])) {

			    addByRetraction(tables[i][i+len],
					    tables[i+1][i+len],
					    superSorts[0],
					    subSorts[0]);

			}
		    }
		}

		// handle ~setsort~
		if (len > 4) {
		    String string = (String)tokens.get(i);		   
		    if (string.equals("~setsort~")) {
			String lp = (String)tokens.get(i+1);
			String rp = (String)tokens.get(i+len);
			String sortName = (String)tokens.get(i+2);
			String comma = (String)tokens.get(i+3);
			ArrayList terms = tables[i+4][i+len-1];
			
			if (lp.equals("(") &&
			    rp.equals(")") &&
			    comma.equals(",")) {
			    
			    Sort[] sorts = sig.getSortsByName(sortName);
			    for (int j=0; j<sorts.length; j++) {
				for (int l=0; l<terms.size(); l++) {
				    try {
					Term term1 = (Term)terms.get(l);
					Operation sortOp = 
					    new Operation(sorts[j].getName(),
						  new Sort[]{},
						  BoolModule.univSort,
						  BOBJModule.getModuleName());
					
					
					Term term2 = new Term(sortOp);
					Operation op =
					    BOBJModule.getSetsortOperation();
					Term term =
					    new Term(sig,
						     op,
						     new Term[]{term2, term1});
					
					tables[i][i+len].add(term);
				    } catch (Exception e){
				    }
				}
			    }

			}
			
		    }
		} // end of handling ~setsort~

		// handle ~sort~
                if (len > 2) {
		    String string = (String)tokens.get(i);		   
		    if (string.equals("~sort~") ||
			string.equals("~sort*~")) {
			
			String lp = (String)tokens.get(i+1);
			String rp = (String)tokens.get(i+len);
			ArrayList terms = tables[i+2][i+len-1];
			
			if (lp.equals("(") &&
			    rp.equals(")") &&
			    sig.containsSystemSort(QidlModule.idSort)) {
			    
			    for (int l=0; l<terms.size(); l++) {

				Term term = (Term)terms.get(l);
				Operation op ;
				if (string.equals("~sort~")) {
				    op = BOBJModule.getSortOperation();
				} else {
				    op = BOBJModule.getFinalSortOperation();
				}
								
				try {
				  term = new Term(sig,
						  op,
						  new Term[]{term});
				  tables[i][i+len].add(term);
				} catch (Exception e) {
				}
				
			    }
			}
			
		    }
		} // end of handling ~sort~
	    }
	}

	return tables[0][tokens.size()-1];

    }


    private void addByRetraction(ArrayList dest,
				 ArrayList list,
				 Sort superSort,
				 Sort subSort) {

	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    if (term.getPropertyBy("()") != null &&
		sig.isSubsort(term.sort, superSort)) {
		try {
		    Sort[] args = new Sort[] { superSort };
		    Sort res = subSort;
		    Operation retOp = new Operation("r:"+superSort.getName()+
						    ">"+subSort.getName()+
						    "(_)",
						    args,
						    res,
						    BOBJModule.getModuleName());
		    retOp.info = "system-retract";
		    
		    term = new Term(sig, 
				    retOp, 
				    new Term[] {term});
		    dest.add(term);
		    //sig.explicitRetract = true;
		    
		} catch (Exception e) {}
	    }
	}

    }

    
    private void addByModuleName(ArrayList dest,
				 ArrayList list,
				 ModuleName modName) 
    {
	
	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    Operation op = term.getTopOperation();
	    
	    if (op == null) continue;

	    // use sort restriction
	    if (modName.op == ModuleName.ATOM) {
		Sort opSort = op.resultSort;
		String reg = modName.atom;
		
		for (int j=0; j<sig.sorts.size(); j++) {
		    Sort sort = (Sort)sig.sorts.elementAt(j);
		    if (sort.getName().equals(reg)) {
			if (sig.isSubsort(opSort, sort)) {
			    dest.add(term);
			}
			break;
		    }    
		}
	    }
	    
	    // use module expression restriction
	    if (op.getModuleName().equals(modName) &&
		!dest.contains(term)) {
		dest.add(term);
	    } else if (((Module)sig).hasParameter(modName.atom) &&
		       op.modName != null &&
		       op.modName.op == modName.ANNOTATE &&
		       op.modName.atom.equals(modName.atom)) {
		if (term.isComposite()) {
		    if (term.getPropertyBy("()") != null ) {
			add(dest, term);
		    }
		} else {
		    add(dest, term);    
		}
	    } else if (((Module)sig).hasParameter(modName.atom) &&
		       op.modName != null &&
		       op.modName.op == modName.ATOM &&
		       op.resultSort.isInitial()) {

		try {
		    
		    Module mod = ((Module)sig).getParameter(modName.atom);
		    if ( mod.containsSort(op.resultSort)) {
		    		
			if (term.isComposite()) {
			    if (term.getPropertyBy("()") != null ) {
				add(dest, term);
			    }
			} else {
			    add(dest, term);    
			}
		    }
		} catch (ModuleParameterException e){
		}
		
		
            } else {
				
		Operation[] ops = sig.getOperationsWithName(op.getName());
		ArrayList l = new ArrayList();
		
		for (int k=0; k<ops.length; k++) {
		    if (ops[k].getModuleName().equals(modName) &&
			op.less(sig, ops[k])) {

			// insert ops[k] into l
			boolean found = false;
			for (int j=0; j<l.size(); j++) {
			    Operation o = (Operation)l.get(i);
			    if (ops[k].less(sig, o)) {
				// remove o
				l.remove(j);
				// insert k
				l.add(ops[k]);
				found = true;
				break;
			    } else if (o.less(sig, ops[k])) {
				found = true;
				break;
			    } 
			}

			if (!found) {
			    l.add(ops[k]);
			}
			
		    }
		}

		try {
		    Term[] terms = term.getSubterms();
		    for (int k=0; k<l.size(); k++) {
			Operation o = (Operation)l.get(k);
			Term t = new Term(sig, o, terms);
			dest.add(t);
		    }
		} catch (TermException ex){
		}
	    }
	}

		
    }
    
    

    private void addAll(int begin, int end, ArrayList dest, ArrayList list)
    {
	
	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    add(dest, term);
	}
	
	if (dest.size() > 1) {

	    ArrayList l = Term.checkRetract(dest);
	    if (l.size() > 1) {
		ArrayList ll =  Term.checkPriority(l);
		if (ll.size() == 0) {
                    // use l 
		} else if (ll.size() > 0) {
		    l = ll;
		}
	    } else if (l.size() == 0) {
		return;
	    } 

	    /*
	    boolean okay = false;
	    for (int i=end+1; i<tokens.size(); i++) {
		String token = (String)tokens.get(i);
		if (!token.equals(")")) {
		    if (token.equals(".")) {
			okay = true;
		    }
	        }
	    }
	    
	    if (!okay) {
	        for (int i=0; i<l.size(); i++) {
		    Term t1 = (Term)l.get(i);
		    for (int j=i+1; j<l.size(); j++) {
			Term t2 = (Term)l.get(j);

			if (t1.sort.equals(t2.sort)) {
			    throw new TermParseException(t1, t2);
			}
		    }
	        }
	    }
	    */
    
	    dest.clear();
	    dest.addAll(l);

	}
	
    }

    
    private void add(ArrayList dest, Term term) {
	
	for (int i=0; i<dest.size(); i++) {
	    Term t = (Term)dest.get(i);

	    if (term.equals(sig, t)) {
				
		if (t.needHeadRetract()) {
		    if (!term.needHeadRetract()) {
						
			dest.remove(i);
			for (int k=dest.size()-1; k >=i; k--) {
			    Term tmp = (Term)dest.get(k);
			    if (removable(term, tmp)) {
				dest.remove(k);
			    }
			}
			dest.add(term);
			return;
		    } else {
			return;
		    }
		    
		} else if (!term.needHeadRetract()) {
		    
		    if (term.operation != null &&
			t.operation != null &&
			term.operation.less(sig, t.operation)) {

			dest.remove(i);
			for (int k=dest.size()-1; k >=i; k--) {
			    Term tmp = (Term)dest.get(k);
			    if (removable(term, tmp)) {
				dest.remove(k);
			    }
			}
			dest.add(term);
		    }  
		    
		    return;
		} else {
		    return;
		}
		
	    } else {
				
		if (t.toString().equals(term.toString())) {
		    
		    if (t.needHeadRetract() && !term.needHeadRetract()) {

			dest.remove(i);
			for (int k=dest.size()-1; k >=i; k--) {
			    Term tmp = (Term)dest.get(k);
			    if (removable(term, tmp)) {
				dest.remove(k);
			    }
			}
			dest.add(term);
			return;
		    } else if (!t.needHeadRetract() && term.needHeadRetract()){

			return;
			
		    }
		    
		} 	    
	    }
	}

	dest.add(term);
	
    }



    private boolean removable(Term term, Term target) {

	if (term.equals(sig, target)) {
	    if (target.needRetract()) {
		if (!term.needRetract()) {
		    return true;
		} else {
		    return false;
		}
		
	    } else if (!term.needRetract()) {
		if (term.operation != null &&
		    target.operation != null &&
		    term.operation.less(sig, target.operation)) {
		    return true;
		} else {
		    return false;
		}
	    } else {
		return false;
	    }
		
	} else {
		
	    if (target.toString().equals(term.toString())) {
		if (target.needRetract() && !term.needRetract()) {
		    return true;
		} else if (!target.needRetract() && term.needRetract()) {
		    return false;
		} else {
		    return false;
		}
	    }
		    
	}

	return false;
	
    }
    
	
    
    private void addAllWithParenthese(ArrayList dest, ArrayList list) {
	for (int i=0; i<list.size(); i++) {
	    Term term = (Term)list.get(i);
	    term.setProperty("()", "*");
	    add(dest, term);
	}
    }


    private void getAllTopMatches(int x,
				  int y,
				  ArrayList ops,
				  ArrayList matches) {
	
	for (int i=0; i<operations.length; i++) {
	    ArrayList list = getAllTopMatches(operations[i], x, y);
	    if (list != null) {
		ops.add(operations[i]);
		matches.add(list);
	    }
	}

    }


    private ArrayList getAllTopMatches(Operation op, int x, int y) {
	Vector opTokens = op.getTokens();
	return getAllTopMatches(opTokens, x, y);
    }


    private ArrayList  getAllTopMatches(Vector vec, int x, int y) {
	
	if (vec.size() > 0 && x <= y) {
	    Object obj = (Object)vec.elementAt(0);
	    vec.removeElementAt(0);
	    
	    if (obj instanceof String) {

		String string = ((String)obj).trim();
		String token =  (String)tokens.get(x); //trim();
			
		if (string.equals(token)) {
		    return getAllTopMatches(vec, x+1, y);
		} else {
		    return null;
		}

	    } else if (obj instanceof Sort) {

		Sort sort = (Sort)obj;
		ArrayList result = new ArrayList();
		for (int i=x; i+vec.size()-1 < y; i++) {

		    if (paratheses[x] != paratheses[i]) {
			continue;
		    }
		    
		    Match match = new Match(x, i, sort);

		    Vector tmp = (Vector)vec.clone();
		    ArrayList list = getAllTopMatches(tmp, i+1, y);
		    if (list != null) {
			
			if (list.size() == 0) {
			    result.add(new Match[]{match});
			} else {

			    for (int j=0; j<list.size(); j++) {
				Match[] mt = (Match[])list.get(j);
			    
				Match[] res = new Match[mt.length+1];
				res[0] = match;
				System.arraycopy(mt, 0, res, 1, mt.length);
				result.add(res);
			    }
			}
		    }
		}

		return result;
	    }
	} else if (vec.size() == 0 ){
	    if (x <= y) {
		return null;
	    } else {
		return new ArrayList();
	    }
	} 
	return null;
       

    } 


    private ArrayList select(int x, int y, Sort sort) {
	
	ArrayList result = new ArrayList();
	for (int i=0; i<tables[x][y].size(); i++) {
	    Term term = (Term)tables[x][y].get(i);
	    Term tmp = term.copy(sig);
            tmp.helper = (Hashtable)term.helper.clone();
	    
	    if (term.parent != null) {
		tmp.parent = null;
	    }
	    term = tmp;
	    
	    if (sig.isSubsort(term.getSort(), sort) ||
		sig.isSubsort(sort, term.getSort()) ||
		sig.hasCommonSupersort(term.getSort(), sort)) {

		result.add(term);
	    } else {

		if (sig.canApply(sort, term.getSort()) != null) {
		    result.add(term);    
		}
		
	    }
	    
	}
	return result;
    }


    private ArrayList join(Operation op, ArrayList candidate) {
		
	ArrayList result = new ArrayList();
		
	ArrayList list = join(candidate);
	
	for (int i=0; i<list.size(); i++) {
	    
	    Term[] terms = (Term[])list.get(i);
	    
	    // handle gather
	    boolean okay = true;
	    for (int j=0; j<terms.length; j++) {
				
		if (op.gather != null && terms[j].operation != null) {
		    if (op.gather[j].equals("E") &&
			op.priority < terms[j].operation.priority &&
			!terms[j].operation.isConstant() &&
			terms[j].getPropertyBy("()") == null ) {
						
			okay = false;
			break;
					    			
		    } else if (op.gather[j].equals("e") &&
			       op.priority <= terms[j].operation.priority &&
			       !terms[j].operation.isConstant()&&
			       terms[j].getPropertyBy("()") == null ) {

		        okay = false;
			break;
			
		    }
		}
	    }

	    if (!okay) continue;
	    
	    try {

		// check whether violates priority definition
		// if op has higher priority than top of terms[last], and 
		//    terms[last] has no parenthese
		//    top of terms[last] has mix notation 
		//    top of terms[last] is front open
		// then term is not okay
		
		Operation oper = terms[terms.length-1].getTopOperation();
		Term term = new Term(sig, op, terms);
				
		if (op.equals(BoolModule.metaIf) &&
		    op.info.equals("system-default")) {
		    
		    if (sig.isSubsort(terms[1].sort, terms[2].sort)) {
			term.sort = terms[2].sort;
		    }

		    if (sig.isSubsort(terms[2].sort, terms[1].sort)) {
			term.sort = terms[1].sort;
		    }
		}
		
		if (oper != null && 
		    op.getPriority() < oper.getPriority() &&
		    op.getName().trim().endsWith("_") &&
		    oper.getName().trim().startsWith("_") &&
		    terms[terms.length-1].getPropertyBy("()") == null) {

		    try {
			Term[] a = new Term[op.getArity()];
			Term[] b = new Term[oper.getArity()];

			System.arraycopy(terms, 0, a, 0, terms.length-1);
			a[terms.length-1] = terms[terms.length-1].subterms[0];

			b[0] = new Term(sig, op, a);
			System.arraycopy(terms[terms.length-1].subterms, 
					 1, 
					 b, 
					 1, 
				     terms[terms.length-1].subterms.length-1);

			Term tmp = new Term(sig, oper, b);
			continue;

		    } catch (Exception e) {
		    }
		    
		}

		oper = terms[0].getTopOperation();

		if (oper != null && 
		    op.getPriority() < oper.getPriority() &&
		    op.getName().trim().startsWith("_") &&
		    oper.getName().trim().endsWith("_") &&
		    terms[0].getPropertyBy("()") == null) {

		    try {
			Term[] a = new Term[op.getArity()];
			Term[] b = new Term[oper.getArity()];

			System.arraycopy(terms, 1, a, 1, terms.length-1);
			a[0] = terms[0].subterms[terms[0].subterms.length-1];

			b[b.length-1] = new Term(sig, op, a);
			System.arraycopy(terms[0].subterms, 
					 0, 
					 b, 
					 0,
				         terms[0].subterms.length-1);

			Term tmp = new Term(sig, oper, b);
			continue;

		    } catch (Exception e) {}
		    
		}	

		result.add(term);
		
	    } catch (Exception e) {}
	    
	}
	
	
	return result;
    }


    private ArrayList join(ArrayList candidate) {
	
	ArrayList result = new ArrayList();

	if (candidate.size() == 1) {
	    ArrayList list = (ArrayList)candidate.get(0);
	    for (int i=0; i<list.size(); i++) {
		Term[] objs = new Term[]{(Term)list.get(i)};
		result.add(objs);
	    }
	    return result;

	} else {
	    ArrayList list = (ArrayList)candidate.get(0);
	    candidate.remove(0);
	    candidate = join(candidate);

	    for (int i=0; i<list.size(); i++) {
		Term obj = (Term)list.get(i);
		for (int j=0; j<candidate.size(); j++) {
		    Term[] objs = (Term[])candidate.get(j);
		    Term[] res = new Term[objs.length+1];
		    res[0] = obj;
		    System.arraycopy(objs, 0, res, 1, objs.length);

		    result.add(res);
		}
	    }

	    return result;
	}
    }


    public void show() {

	System.out.println("\n--------- show ------------");
	System.out.println("tokens = "+tokens);
	for (int i=0; i<tokens.size(); i++) {
	    for (int j=i; j<tokens.size(); j++) {
		if (tables[i][j] != null && tables[i][j].size() != 0) {
		    System.out.println(i+"   "+j+" : "+tables[i][j]);
		}
	    }
	}
    }


    
    public String[] getUnknownTokens() 
    {
	ArrayList list = new ArrayList();
	for (int i=0; i<tokens.size(); i++) {
	    String string = (String)tokens.get(i);
	    if (!sig.tokens.contains(string) &&
		!string.equals(",") &&
		!string.equals("(") &&
		!string.equals(")")) {
		list.add(tokens.get(i));
	    }
	}

	String[] result = new String[list.size()];
        for (int i=0; i<list.size(); i++) {
	    result[i] = (String)list.get(i);
	}        

	return result;
	
    }
    
    
    class Match {
	int x;
	int y;
	Sort sort;

	public Match(int x, int y, Sort sort) {
	    this.x = x;
	    this.y = y;
	    this.sort = sort;
	}

	public String toString() {
	    return "("+x+" "+y+" "+sort.getName()+")";
	}
    }

}









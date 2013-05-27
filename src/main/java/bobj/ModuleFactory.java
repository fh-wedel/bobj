
package bobj;

import java.util.*;

public class ModuleFactory 
{

    static Module bool = createBool();
    
    public static Module createTruthValue() {

	ModuleName modName = new ModuleName("TRUTH-VALUE");
	Module result = new Module(Module.INITIAL, modName);
	
	try {
     
	    Sort bool = new Sort("Bool", modName);
	    bool.setInfo("system-default");
	    result.addSort(bool);
	    
	    Operation trueOp = new Operation("true", bool, modName);
	    trueOp.setInfo("system-default");
	    result.addOperation(trueOp);

	    Operation falseOp = new Operation("false", bool, modName);
	    falseOp.setInfo("system-default");
	    result.addOperation(falseOp);
	    
	} catch (Exception e) { }

	return result;
	
    }

 
    public static Module createTruth() {

	ModuleName modName = new ModuleName("TRUTH");
	Module result = new Module(Module.INITIAL, modName);
    
	try {
	    Module tmp = createTruthValue();
	    result.protectedImport(tmp);
	    
	    Sort bool = (Sort)result.sorts.elementAt(0);
	    Operation trueOp = (Operation)result.operations.elementAt(0);
	    Operation falseOp = (Operation)result.operations.elementAt(1);
	    
	    // define sort Universal
	    Sort universal = new Sort("Universal", modName);
	    universal.setInfo("system-default");
	    result.addSort(universal);
	    result.addSubsort(universal,bool);

	    // define operation _==_
	    Operation eqOp = new Operation("_ == _",
					   new Sort[]{ universal, universal},
					   bool,
					   modName);
	    eqOp.setInfo("system-default");
	    eqOp.setPriority(2);
	    result.addOperation(eqOp); 

	    
            // define equation about _ == _
	    Variable x = new Variable("X", universal);
	    result.addVariable(x);

	    Equation eq1 = new Equation(new Term(eqOp,
						 new Term[] { new Term(x),
							      new Term(x) }),
					new Term(trueOp));
	    eq1.setInfo("system-default");

	    //result.addEquation(eq1);
	    result.equations.add(eq1);
	    
	    // define operation _=/=_
	    Operation neqOp = new Operation("_ =/= _",
					    new Sort[]{ universal, universal},
					    bool,
					    modName);
	    neqOp.setInfo("system-default");
	    neqOp.setPriority(2);
	    result.addOperation(neqOp); 	    

	    // define if_then_else_fi
	    Operation ifOp = new Operation("if_then_else_fi",
					   new Sort[] { bool,
							universal,
							universal},
					   universal,
					   modName);
	    ifOp.setInfo("system-default");
	    result.addOperation(ifOp);

	    Variable y = new Variable("Y", universal);
	    result.addVariable(y);

	    // add equation if true then X else Y final = X 
	    Equation eq2 = new Equation(new Term(ifOp,
						 new Term[]{ new Term(trueOp),
							     new Term(x),
							     new Term(y)}),
					new Term(x));
	    eq2.setInfo("system-default");
	    result.equations.add(eq2);
	    //result.addEquation(eq2);

	    //add equation if false then X else Y final = Y 
	    Equation eq3 = new Equation(new Term(ifOp,
						 new Term[]{ new Term(falseOp),
							     new Term(x),
							     new Term(y)}),
					new Term(y));
	    eq3.setInfo("system-default");
	    //result.addEquation(eq3);
            result.equations.add(eq3);
	    
	    // equation if B then X else X = X .
	    Variable b = new Variable("B", bool);
	    result.addVariable(b);
	    Equation eq4 = new Equation(new Term(ifOp,
						 new Term[]{ new Term(b),
							     new Term(x),
							     new Term(x)}),
					new Term(x));
	    eq4.setInfo("system-default");
	    //result.addEquation(eq4);	    
	    result.equations.add(eq4);
	    
	} catch (SignatureException e) { 
	} catch (TermException e) {
	}

	return result;      

    }


    
    public static Module createBool() {

	ModuleName modName = new ModuleName("BOOL");
	Module result = new Module(Module.INITIAL, modName);
	
	try {

	    result.protectedImport(createTruth());
	    
	    Sort bool = (Sort)result.sorts.elementAt(0);
	    Operation trueOp = (Operation)result.operations.elementAt(0);
	    Operation falseOp = (Operation)result.operations.elementAt(1);

	    // add operation and
	    Operation and = new Operation("_ and _",
					  new Sort[] {bool, bool},
					  bool,
					  modName);
	    and.setPriority(20);
	    and.setInfo("system-default");
	    and.setAssociativity();
	    and.setCommutativity();
	    result.addOperation(and);

	    // add operation or
	    Operation or = new Operation("_ or _",
					 new Sort[] {bool, bool},
					 bool,
					 modName);
	    or.setPriority(30);
	    or.setInfo("system-default");
	    or.setAssociativity();
	    or.setCommutativity();
	    result.addOperation(or);

	    // add operation xor
	    Operation xor = new Operation("_ xor _",
					  new Sort[] {bool, bool},
					  bool,
					  modName);
	    xor.setInfo("system-default");
	    xor.setAssociativity();
	    xor.setCommutativity();
	    result.addOperation(xor);

	    // add operation implies
	    Operation implies = new Operation("_ implies _",
					      new Sort[] {bool, bool},
					      bool,
					      modName);
	    implies.setInfo("system-default");
	    result.addOperation(implies);

	    // add operation not 
	    Operation not = new Operation("not _",
					  new Sort[] {bool},
					  bool,
					  modName);
	    not.setPriority(10);
	    not.setInfo("system-default");
	    result.addOperation(not);
 
	    // create three terms for use later
	    Term trueTerm = new Term(trueOp);
	    Term falseTerm = new Term(falseOp);
	    Term b = new Term(new Variable("B", bool));
	    Term b1 = new Term(new Variable("B1", bool));
	    Term b2 = new Term(new Variable("B2", bool));
	    
	    // equation: not true = false
	    Equation eq = new Equation(new Term(not,
						new Term[]{trueTerm}),
				       falseTerm);
            eq.setInfo("system-default");
	    result.equations.add(eq);

	    // eqaution: not false = true
	    eq = new Equation(new Term(not,
				       new Term[]{falseTerm}),
			      trueTerm);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation: true and B = B .
	    eq = new Equation(new Term(and,
				       new Term[] {trueTerm,
						   b}),
			      b);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation: false and B = false .
	    eq = new Equation(new Term(and,
				       new Term[] {falseTerm,
						   b}),
			      falseTerm);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation: true or B = true
	    eq = new Equation(new Term(or,
				       new Term[] {trueTerm, b}),
			      trueTerm);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation: false or B = B
	    eq = new Equation(new Term(or,
				       new Term[] {falseTerm,
						   b}),
			      b);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation: B1 implies B2 = (not B1) or B2
	    Term left = new Term(implies, new Term[] {b1, b2});
	    Term right = new Term(or,
				  new Term[] { new Term(not, new Term[] {b1}),
					       b2 });
	    eq = new Equation(left, right);
	    eq.setInfo("system-default");
	    result.equations.add(eq);
	    
	} catch (SignatureException e) { 
	} catch (TermException e) {}
    
	return result;

    }


    public static Module createQid() {

	ModuleName modName = new ModuleName("QID");
	Module result = new Module(Module.INITIAL, modName);

	try {
	    result.protectedImport(createBool());
	    Sort id = new Sort("Id", modName);
	    id.setInfo("system-default");
	    result.addSort(id);

	    java.util.List list = new java.util.ArrayList();
	    list.add(id);
	    result.alias.put("QID", list);

	} catch (SignatureException e) { 
	} 
	
	return result;
    }

    
    public static Module createNzNat() {

	ModuleName modName = new ModuleName("NZNAT");
	Module result = new Module(Module.INITIAL, modName);

	try {
	    result.protectedImport(createBool());
	    Sort bool = (Sort)result.sorts.elementAt(0);

	    Sort nznat = new Sort("NzNat", modName);
	    nznat.setInfo("system-default");
	    result.addSort(nznat);

	    Operation add = new Operation("_ + _",
					  new Sort[] {nznat, nznat},
					  nznat,
					  modName);
	    add.setInfo("system-default");
	    add.setAssociativity();
	    add.setCommutativity();
	    result.addOperation(add);

	    Operation succ = new Operation("s _",
					   new Sort[] {nznat},
					   nznat,
					   modName);
	    succ.setInfo("system-default");
	    result.addOperation(succ);

	} catch (SignatureException e) { }
 
	return result;
    }




    public static Module createNat() {

	ModuleName modName = new ModuleName("NAT");
	Module result = new Module(Module.INITIAL, modName);
    
	try {

	    result.importModule(createBool());

	    Sort nat = new InitialSort("Nat", modName);
	    nat.setProperty("info", "system-default");
	    result.addSort(nat);
	    
	    Sort z = new Sort("Zero", modName);
	    z.setProperty("info", "system-default");
	    result.addSort(z);

	    result.protectedImport(createNzNat());

	    Sort bool = (Sort)result.sorts.elementAt(0);
	    Sort nznat = (Sort)result.sorts.elementAt(4);
	    result.addSubsort(nat, nznat);
	    result.addSubsort(nat, z);

	    Operation t = (Operation)result.operations.elementAt(0);
	    Operation f = (Operation)result.operations.elementAt(1);
	    Operation or = (Operation)result.operations.elementAt(6);
	    Operation and = (Operation)result.operations.elementAt(5);
	    Operation not = (Operation)result.operations.elementAt(9);
	    
	    Operation zero = new Operation("0", z, modName);
	    zero.setInfo("system-default");
	    result.addOperation(zero);

	    Operation succ = new Operation("s _",
					   new Sort[] {nat},
					   nznat,
					   modName);
	    succ.setInfo("system-default");
	    result.addOperation(succ);

	    Operation pred = new Operation("p _",
					   new Sort[]{nznat},
					   nat,
					   modName);
	    pred.setInfo("system-default");
	    result.addOperation(pred);

	    Sort[] b = {nat, nat};
	    Operation less = new Operation("_ > _", b, bool, modName);
	    less.setInfo("system-default");
	    result.addOperation(less);

	    Operation greater = new Operation("_ < _", b, bool, modName);
	    greater.setInfo("system-default");
	    result.addOperation(greater);

	    Operation geq = new Operation("_ <= _", b, bool, modName);
	    geq.setInfo("system-default");
	    result.addOperation(geq);

	    Operation leq = new Operation("_ >= _", b, bool, modName);
	    leq.setInfo("system-default");
	    result.addOperation(leq);
      
	    Operation add = new Operation("_ + _", b, nat, modName);
	    add.setAssociativity();
	    add.setCommutativity();
	    add.setInfo("system-default");
	    result.addOperation(add);

	    Operation mult = new Operation("_ * _", b, nat, modName);
	    mult.setAssociativity();
	    mult.setCommutativity();
	    mult.setInfo("system-default");
	    mult.setPriority(30);
	    result.addOperation(mult);

	    Operation div = new Operation("_ div _", b, bool, modName);
	    div.setInfo("system-default");
	    div.setPriority(30);
	    result.addOperation(div);

	    Operation equal = new Operation("eq", b, bool, modName);
	    equal.setInfo("system-default");
	    result.addOperation(equal);
  
	    Variable n = new Variable("N", nat);
	    result.addVariable(n);

	    Variable m = new Variable("M", nat);
	    result.addVariable(m);

	    Equation eq;

	    // equation 0 > N = false
	    Term r1 = new Term(f, new Term[0]);
	    Term l1 = new Term(result,
			       less,
			       new Term[] {new Term(result,
						    zero,
						    new Term[0]),
					   new Term(n) });
	    eq = new Equation(l1, r1); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation s N > 0 = true
	    Term l2 = new Term(result,
			       less,
			       new Term[] {new Term(succ,
						    new Term[] {new Term(n)}),
					   new Term(zero, new Term[0])
					   }
			       );
	    Term r2 = new Term(t, new Term[0]);
	    eq = new Equation(l2, r2); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation s N > s M = N > M 
	    Term l3 = new Term(result,
			       less,
			       new Term[] { new Term(succ,
						     new Term[] {new Term(n)}),
					    new Term(succ,
						     new Term[] {new Term(m)})
					  }
			       );
	    Term r3 = new Term(result,
			       less,
			       new Term[] { new Term(n), new Term(m) });

	    eq = new Equation(l3, r3); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);


	    // equation eq(N, N) = true
	    Term l4 = new Term(result,
			       equal,
			       new Term[] { new Term(n), new Term(n) });
	    Term r4 = new Term(t, new Term[0]);
	    eq = new Equation(l4, r4); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);


	    // equation eq(0, s N) = false
	    Term l5 = new Term(result,
			       equal,
			       new Term[]
		{new Term(zero, new Term[0]),
		 new Term(succ, new Term[] {new Term(n)}) }
			       );
	    Term r5 = new Term(f, new Term[0]);
	    eq = new Equation(l5, r5); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation eq(s N, 0) = false
	    Term l6 = new Term(result,
			       equal,
			       new Term[]
		{ new Term(succ, new Term[] {new Term(n)}),
		  new Term(zero, new Term[0])}
			       );
	    Term r6 = new Term(f, new Term[0]);
	    eq = new Equation(l6, r6); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation eq(s N, s M) = eq(N, M) 
	    Term l7 = new Term(result,
			       equal,
			       new Term[]
		{ new Term(succ, new Term[] {new Term(n)}),
		  new Term(succ, new Term[] {new Term(m)}) }
			       );
	    Term r7 = new Term(result,
			       equal,
			       new Term[]
		{new Term(n) , new Term(m)}
			       );
	    eq = new Equation(l7, r7); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

      
	    // equation eq(N, M) = false if N < M or M < N
	    Term l9 = new Term(equal,
			       new Term[] {new Term(n) , new Term(m)} 
			       );
	    Term r9 = new Term(f, new Term[0]);
	    Term c9 = new Term(or,
			       new Term[]
		{
		    new Term(greater, new Term[]{ new Term(n) ,
						  new Term(m) }),
		    new Term(greater, new Term[]{ new Term(m) ,
						  new Term(n) })
			}
			       );
	    eq = new Equation(c9, l9, r9); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation M < 0 = false
	    Term r10 = new Term(f, new Term[0]);
	    Term l10 = new Term(result,
				greater,
				new Term[] { new Term(m),
					     new Term(result,
						      zero,
						      new Term[0])
						 }
				);
	    eq = new Equation(l10, r10); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation 0 < s N = true
	    Term r11 = new Term(t, new Term[0]);
	    Term l11 = new Term(result,
				greater,
				new Term[] 
		                    {  new Term(zero, new Term[0]),
		                       new Term(succ, new Term[] {new Term(n)})
			            }
				);
	    eq = new Equation(l11, r11); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // equation s N < s M = N > M 
	    Term l12 = new Term(result,
				greater,
				new Term[]
		                   { new Term(succ, new Term[] {new Term(n)}),
		                     new Term(succ, new Term[] {new Term(m)})
				   }
				);
	    Term r12 = new Term(result,
				greater,
				new Term[] { new Term(n), new Term(m) });
	    eq = new Equation(l12, r12); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // eq geq(N, s M) = N > M .
	    Term l13 = new Term(result,
				geq,
				new Term[] {
				    new Term(succ,
					     new Term[]{new Term(m)}),
				    new Term(n)}
				);
	    Term r13 = new Term(greater, new Term[]{new Term(m) ,
						    new Term(n) });
	    eq = new Equation(l13, r13); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);


	    // equation geq(N, M) = eq(N, M) or N > M

	    Term l8 = new Term(geq,
			       new Term[] {new Term(n) , new Term(m)} 
			       );
	    Term r8 = new Term(or,
			       new Term[] {
				   new Term(equal, new Term[]{new Term(n) ,
							      new Term(m) }),
				   new Term(greater, new Term[]{new Term(n) ,
								new Term(m) }),
			       });
	    eq = new Equation(l8, r8); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);
      
	    // 0 > N = false
	    Term l15 = new Term(result,
				less,
				new Term[] { new Term(zero, new Term[0]) ,
					     new Term(n)} 
				);
	    Term r15 = new Term(f, new Term[0]);
	    eq = new Equation(l15, r15); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);      

	    // s N > s M = N > M
	    Term l16 = new Term(result,
				less,
				new Term[]
		{ new Term(succ, new Term[] {new Term(n)}),
		  new Term(succ, new Term[] {new Term(m)}) });
	    Term r16 = new Term(result,
				less,
				new Term[]
		{ new Term(n),
		  new Term(m) });
	    eq = new Equation(l16, r16); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);
      
	    // s N > 0 = true
	    Term l17 = new Term(result,
				less,
				new Term[]
		{
		    new Term(succ, new Term[] {new Term(m)}),
		    new Term(zero, new Term[0]),
		});
	    Term r17 = new Term(t, new Term[0]);
	    eq = new Equation(l17, r17); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);


	    // N >= 0 = true
	    Term l18 = new Term(result,
				leq,
				new Term[] { new Term(n),
					     new Term(zero, new Term[0])} 
				);
	    Term r18 = new Term(t, new Term[0]);
	    eq = new Equation(l18, r18); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);
      
	    // s N >= s M = N >= M
	    Term l19 = new Term(result,
				leq,
				new Term[]{ new Term(succ,
						     new Term[] {new Term(n)}),
					    new Term(succ,
						     new Term[] {new Term(m)})
					   }
				);
	    Term r19 = new Term(result,
				leq,
				new Term[] { new Term(n), new Term(m) });
	    eq = new Equation(l19, r19); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // 0 >= s N = false
	    Term l20 = new Term(result,
				leq,
				new Term[] { new Term(zero, new Term[0]) ,
					     new Term(succ,
						      new Term[]{new Term(n)})
						 }
				);
	    Term r20 = new Term(f, new Term[0]);
	    eq = new Equation(l20, r20); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);
      
	    // N >= N = true
	    Term l21 = new Term(result,
				leq,
				new Term[] { new Term(n) ,
					     new Term(n)
						 }
				);
	    Term r21 = new Term(t, new Term[0]);
	    eq = new Equation(l21, r21); 
	    eq.setInfo("system-default");
	    result.equations.add(eq);      
            
	    // p s N = N
	    Term r22 = new Term(n);
	    Term l22 = new Term(result,
			       pred,
			       new Term[]{
				   new Term(result,
					    succ,
					    new Term[]{ new Term(n) }
					    )
				       }
			       );
            eq = new Equation(l22, r22);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    
	} catch (SignatureException e) {
	} catch (TermException e) {
	}
 
	return result;
    }



    public static Module createInt() {

	ModuleName modName = new ModuleName("INT");
	Module result = new Module(Module.INITIAL, modName);
    
	try {

	    result.protectedImport(createBool());
	    
	    Sort inte = new Sort("Int", modName);
	    inte.setInfo("system-default");
	    result.addSort(inte);

	    Sort nzint = new Sort("NzInt", modName);
	    nzint.setInfo("system-default");
	    result.addSort(nzint);
	    
	    result.protectedImport(createNat());

	    Sort bool = (Sort)result.sorts.elementAt(0);
	    Sort nat = (Sort)result.sorts.elementAt(4);
	    Sort nznat = (Sort)result.sorts.elementAt(6);
	    
	    result.addSubsort(inte, nat);
	    result.addSubsort(nzint, nznat);
	    result.addSubsort(inte, nzint);

	    Operation zero = (Operation)result.operations.elementAt(11);
	    
	    Sort[] a1 = new Sort[1];
	    a1[0] = inte;

	    Operation sub1 = new Operation("- _", a1, inte, modName);
	    sub1.setPriority(20);
	    sub1.setInfo("system-default");
	    result.addOperation(sub1);

	    Operation succ = new Operation("s _", a1,inte, modName);
	    //succ.setPriority(20);              // add 5/2      
	    succ.setInfo("system-default");
	    result.addOperation(succ);
     
	    Operation pred = new Operation("p _", a1, inte, modName);
	    pred.setPriority(20);
	    pred.setInfo("system-default");
	    result.addOperation(pred);
      
	    Sort[] a2 = new Sort[1];
	    a2[0] = nzint;
 
	    Operation sub2 = new Operation("- _", a2, nzint, modName);
	    sub2.setPriority(20);
	    sub2.setInfo("system-default");
	    result.addOperation(sub2);

	    Sort[] a3 = new Sort[2];
	    a3[0] = inte;
	    a3[1] = inte;

	    Operation add = new Operation("_ + _", a3, inte, modName);
	    add.setAssociativity();
	    add.setCommutativity();
	    add.setPriority(40);
	    add.setInfo("system-default");
	    result.addOperation(add);

	    Operation sub3 = new Operation("_ - _", a3, inte, modName);
	    sub3.setPriority(20);
	    sub3.setAssociativity();
	    sub3.setInfo("system-default");
	    result.addOperation(sub3);

	    Operation mult = new Operation("_ * _", a3, inte, modName);
	    mult.setAssociativity();
	    mult.setPriority(30);
	    mult.setInfo("system-default");
	    result.addOperation(mult);

	    Operation less = new Operation("_ < _",a3, bool, modName);
	    less.setInfo("system-default");
	    result.addOperation(less);

	    Operation leq = new Operation("_ <= _",a3, bool, modName);
	    leq.setInfo("system-default");
	    result.addOperation(leq);

	    Operation great = new Operation("_ > _",a3, bool, modName);
	    great.setInfo("system-default");
	    result.addOperation(great);

	    Operation egr = new Operation("_ >= _",a3, bool, modName);
	    egr.setInfo("system-default");
	    result.addOperation(egr);

	    Operation quo = new Operation("_ quo _", a3, inte, modName);
	    quo.setInfo("system-default");
	    result.addOperation(quo);

	    Operation rem = new Operation("_ rem _", a3, inte, modName);
	    rem.setInfo("system-default");
	    result.addOperation(rem);

	    Operation divides = new Operation("_ divides _",
					      a3,
					      inte,
					      modName);
	    divides.setInfo("system-default");
	    result.addOperation(divides);

	    // prepare for equations
      
	    Variable varI = new Variable("I", inte);
	    result.addVariable(varI);

	    Variable varJ = new Variable("J", inte);
	    result.addVariable(varJ);

	    Variable varK = new Variable("K", inte);
	    result.addVariable(varK);

	    Equation eq;

	    // s p I = I
	    Term r1 = new Term(varI);
	    Term l1 = new Term(result,
			       succ,
			       new Term[] {
				   new Term(result,
					    pred,
					    new Term[]{ new Term(varI) }
					    )
				       }
			       );
            eq = new Equation(l1, r1);
	    eq.setInfo("system-default");
	    result.equations.add(eq);
      
	    // p s I = I
	    Term r2 = new Term(varI);
	    Term l2 = new Term(result,
			       pred,
			       new Term[]{
				   new Term(result,
					    succ,
					    new Term[]{ new Term(varI) }
					    )
				       }
			       );
            eq = new Equation(l2, r2);
	    eq.setInfo("system-default");
	    result.equations.add(eq);
	  
	    // I + 0 = I
	    Term r3 = new Term(varI);
	    Term l3 = new Term(result,
			       add,
			       new Term[] {
				   new Term(varI),
				   new Term(result, zero, new Term[0])
				       }
			       );
            eq = new Equation(l3, r3);
	    eq.setInfo("system-default");
	    result.equations.add(eq);      
			 
       
	    // I + s J = s(I + J)
	    Term r4 = new Term(result,
			       succ,
			       new Term[] {
				   new Term(result,
					    add,
					    new Term[] { new Term(varI),
							 new Term(varJ)})
				       }
			       );
	    Term l4 = new Term(result,
			       add,
			       new Term[] {
				   new Term(varI),
				   new Term(result,
					    succ,
					    new Term[] {new Term(varJ)})
				       }
			       );
            eq = new Equation(l4, r4);
	    eq.setInfo("system-default");
	    result.equations.add(eq);      
			     
	    // I + p J = p(I + J)
	    Term r5 = new Term(result,
			       pred,
			       new Term[] {
				   new Term(result,
					    add,
					    new Term[] { new Term(varI),
							 new Term(varJ)})
				       }
			       );
	    Term l5 = new Term(result,
			       add,
			       new Term[] {
				   new Term(varI),
				   new Term(result,
					    pred,
					    new Term[] {new Term(varJ)})
				       }
			       );
            eq = new Equation(l5, r5);
	    eq.setInfo("system-default");
	    result.equations.add(eq);      
      
	    // I * 0 = 0
	    Term r6 = new Term(result,
			       zero,
			       new Term[0]);
	    Term l6 = new Term(result,
			       mult,
			       new Term[] {
				   new Term(varI),
				   new Term(result,
					    zero,
					    new Term[0])
				       });
            eq = new Equation(l6, r6);
	    eq.setInfo("system-default");
	    result.equations.add(eq);      
      
	    // I * s J = I * J + I
	    Term r7 = new Term(result,
			       add,
			       new Term[] {
				   new Term(result,
					    mult,
					    new Term[] { new Term(varI),
							 new Term(varJ)}),
				   new Term(varI)
				       });
	    Term l7 = new Term(result,
			       mult,
			       new Term[] {
				   new Term(varI),
				   new Term(result,
					    succ,
					    new Term[] {new Term(varJ)})
				       });
            eq = new Equation(l7, r7);
	    eq.setInfo("system-default");
	    result.equations.add(eq);         
      

	    // I * p J = I * J - I
	    Term r8 = new Term(result,
			       sub3,
			       new Term[] {
				   new Term(result,
					    mult,
					    new Term[] { new Term(varI),
							 new Term(varJ)}),
				   new Term(varI)
				       });
	    Term l8 = new Term(result,
			       mult,
			       new Term[] {
				   new Term(varI),
				   new Term(result,
					    pred,
					    new Term[] {new Term(varJ)})
				       });
            eq = new Equation(l8, r8);
	    eq.setInfo("system-default");
	    result.equations.add(eq);         
      
	    // I * (J + K) = I * J + I * K
	    Term l9 = new Term(result,
			       mult,
			       new Term[] {
				   new Term(varI),
				   new Term(result,
					    add,
					    new Term[] { new Term(varJ),
							 new Term(varK)})
				       }
			       );
	    Term r9 = new Term(result,
			       add,
			       new Term[] {
				   new Term(result,
					    mult,
					    new Term[] { new Term(varI),
							 new Term(varJ)}),
				   new Term(result,
					    mult,
					    new Term[] { new Term(varI),
							 new Term(varK)})
				       }
			       );
            eq = new Equation(l9, r9);
	    eq.setInfo("system-default");
	    result.equations.add(eq);
      
	    // - - I = I
	    Term r10 = new Term(varI);
	    Term l10 = new Term(result,
				sub1,
				new Term[] {
				    new Term(result,
					     sub1,
					     new Term[]{ new Term(varI) }
					     )
					});
            eq = new Equation(l10, r10);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

      
	    // - s I = p - I
	    Term l11 = new Term(result,
				sub1,
				new Term[] {
				    new Term(result,
					     succ,
					     new Term[]{ new Term(varI) }
					     )
					});
	    Term r11 = new Term(result,
				pred,
				new Term[] {
				    new Term(result,
					     sub1,
					     new Term[]{ new Term(varI) }
					     )
					});
            eq = new Equation(l11, r11);
	    eq.setInfo("system-default");
	    result.equations.add(eq);

	    // - p I = s - I
	    Term l12 = new Term(result,
				sub1,
				new Term[] {
				    new Term(result,
					     pred,
					     new Term[]{ new Term(varI) }
					     )
					});
	    Term r12 = new Term(result,
				succ,
				new Term[] {
				    new Term(result,
					     sub1,
					     new Term[]{ new Term(varI) }
					     )
					});
            eq = new Equation(l12, r12);
	    eq.setInfo("system-default");
	    result.equations.add(eq);      

	    // I - J = I + - J
	    Term l13 = new Term(result,
				sub3,
				new Term[] {
				    new Term(varI),
				    new Term(varJ)
					}
				);
	    Term r13 = new Term(result,
				add,
				new Term[] {
				    new Term(varI),
				    new Term(result,
					     sub1,
					     new Term[] {new Term(varJ)})
					}
				);
            eq = new Equation(l13, r13);
	    eq.setInfo("system-default");
	    result.equations.add(eq);         
            
	    // I + - I = 0
	    Term l14 = new Term(result,
				add,
				new Term[] {
				    new Term(varI),
				    new Term(result,
					     sub1,
					     new Term[] {new Term(varI)})
					}
				);
	    Term r14 = new Term(result,
				zero,
				new Term[0]);
            eq = new Equation(l14, r14);
	    eq.setInfo("system-default");
	    result.equations.add(eq);         
     
	    // -(I + J) = - I - J
	    Term l15 = new Term(result,
				sub1,
				new Term[] {
				    new Term(result,
					     add,
					     new Term[] {
						 new Term(varI),
						 new Term(varJ)
						     })
					});
	    Term r15 =  new Term(result,
				 sub3,
				 new Term[] {
				     new Term(result,
					      sub1,
					      new Term[] {new Term(varI)}),
				     new Term(varJ),
				 });
            eq = new Equation(l15, r15);
	    eq.setInfo("system-default");
	    result.equations.add(eq);          

	    // I * - J = -(I * J) .
	    Term l16 = new Term(result,
				mult,
				new Term[] {   
				    new Term(varI),
				    new Term(result,
					     sub1,
					     new Term[] {
						 new Term(varJ)
						     })
					}
				);
	    Term r16 =  new Term(result,
				 sub1,
				 new Term[] {
				     new Term(result,
					      mult,
					      new Term[] { new Term(varI),
							   new Term(varJ)
							  })
					 }
				 );

            eq = new Equation(l16, r16);
	    eq.setInfo("system-default");
	    result.equations.add(eq);          

	} catch (SignatureException e) {
	} catch (TermException e) {
	}

	return result;
    }



    public static Module createTriv() {

	ModuleName modName = new ModuleName("TRIV");
	Module result = new Module(Module.LOOSE, modName);
	
	try {
	    result.importModule(createTruth());
	    Sort elt = new Sort("Elt", modName);
	    result.addSort(elt);
	    
	} catch (SignatureException e) {}

	return result;
    }



    public static Module createQidl() 
    {
	
	ModuleName modName = new ModuleName("QIDL");
	Module result = new Module(Module.INITIAL, modName);
	
	try {
	    result.importModule(createBool());
	    result.importModule(createQid());

	    Sort boolSort = (Sort)result.sorts.elementAt(0);
	    Sort idSort = (Sort)result.sorts.elementAt(2);

	    Operation less = new Operation("_<_",
					   new Sort[] { idSort, idSort},
					   boolSort,
					   modName);
	    less.setInfo("system-default");
	    result.addOperation(less);	    	    
	    
	} catch (SignatureException e) {}

	return result;
    }
    


    public static Module getDefaultModule(String name) 
    {
	if (name.equals("QID")) {
	    return createQid();
	} else if (name.equals("QIDL")) {
	    return createQidl();    
	} else if (name.equals("TRIV")) {
	    return createTriv();
	} else if (name.equals("NAT")) {
	    return createNat();
	} else if (name.equals("INT")) {
	    return createInt();
	} else if (name.equals("FLOAT")) {
	    return createFloat();	
	} else if (name.equals("BOOL")) {
	    return createBool();
	} else if (name.equals("TRUTH")) {
	    return createTruth();	
	} else if (name.equals("TRUTH-VALUE")) {
	    return createTruthValue();	    
	} else if (name.equals("IDENTICAL")) {
	    return createIdentical();
	} else if (name.endsWith("TUPLE")) {
	    String number = name.substring(0, name.length()-5);
	    try {
		int aInt = Integer.parseInt(number);
		if (aInt > 1) {
		    return createTuple(aInt);
		} else {
		    return null;
		}
	    } catch (Exception e) {
		return null;
	    }
        } else {
	    return null;
	}
		
    }
    

    public static Module createIdentical() {

	ModuleName modName = new ModuleName("IDENTICAL");
	Module result = new Module(Module.LOOSE, modName);
    
	try {
	    Module tmp = createTruth();
	    result.protectedImport(tmp);

	    Sort bool = (Sort)result.sorts.elementAt(0);
	    Sort universal = (Sort)result.sorts.elementAt(1);
	    
	    // define operation _===_
	    Operation eqOp = new Operation("_ === _",
					   new Sort[]{ universal, universal},
					   bool,
					   modName);
	    eqOp.setInfo("system-default");
	    result.addOperation(eqOp); 
	    
	    // define operation _=/==_
	    Operation neqOp = new Operation("_ =/== _",
					    new Sort[]{ universal, universal},
					    bool,
					    modName);
	    neqOp.setInfo("system-default");
	    result.addOperation(neqOp); 	    
	    
	} catch (SignatureException e) { 
	}
	
	return result;             
    }


    public static Module createTuple(int n) {

	if (n <= 1) {
	    return null; 
	}

	ModuleName modName = new ModuleName(n+"TUPLE");
	Module result = new Module(Module.INITIAL, modName);
    
	try {
	    result.importModule(createBool());

	    // create n parameters
	    Module triv = createTriv();
	    for (int i=1; i<=n; i++) {
		result.addParameter("C"+i, triv, new HashMap());
	    }

	    result.levels = new int[] { n };
	    
	    // define sort nTuple
	    InitialSort tuple = new InitialSort("Tuple"+n, modName);
	    result.addSort(tuple);

	    // define operation << ... >>
            String compName = "<<";
	    for (int i=1; i<n; i++) {
		compName += "_;";
	    }
	    compName += "_>>";

	    Sort[] elts = result.getSortsByName("Elt");
	    Sort[] args = new Sort[n];
	    for (int i=0; i<elts.length; i++) {
		args[i] = elts[n-i-1];
	    }

	    Operation comp = new Operation(compName, args, tuple, modName);
	    result.addOperation(comp);
	    
	    // define projection 1* 2* ... n*
	    ArrayList oplist = new ArrayList();
	    for (int i=1; i<=n; i++) {
		Operation proj = new Operation(i+"*_", 
					       new Sort[] { tuple },
					       args[i-1],
					       modName);
		result.addOperation(proj);
		oplist.add(proj);
	    }

	    // define variables e1 : Elt , ..., en : Elt 
	    ArrayList varlist = new ArrayList();
	    Term[] terms = new Term[n];

	    for (int i=1; i<=n; i++) {
		Variable var = new Variable("e"+i, 
					    args[i-1]);
		result.addVariable(var);
	        varlist.add(var);
		terms[i-1] = new Term(var);
	    }

	    // define equations for projections
	    Term share = new Term(comp, terms);
	    for (int i=1; i<=n; i++) {
		Term left = new Term((Operation)oplist.get(i-1),
				     new Term[] { share } );
		Term right = terms[i-1];
		Equation eq = new Equation(left, right);
		result.equations.add(eq);
	    }

	} catch (Exception e) { 
	}
	return result;     

    }


    public static Module createFloat() {
	
	ModuleName modName = new ModuleName("FLOAT");
	Module result = new Module(Module.INITIAL, modName);
    
	try {
	    result.importModule(createBool());
	    
	    Sort floatSort = new Sort("Float", modName);
	    floatSort.setInfo("system-default");
	    result.addSort(floatSort);

	    Sort bool = (Sort)result.sorts.elementAt(0);
	    
	    Sort[] a1 = new Sort[] { floatSort };
	    Sort[] a2 = new Sort[] { floatSort, floatSort };
	    
	    Operation add = new Operation("_ + _", a2, floatSort, modName);
	    add.setAssociativity();
	    add.setCommutativity();
	    add.setPriority(40);
	    add.setInfo("system-default");
	    result.addOperation(add);

	    Operation sub = new Operation("_ - _", a2, floatSort, modName);
	    sub.setAssociativity();
	    sub.setPriority(40);
	    sub.setInfo("system-default");
	    result.addOperation(sub);

	    Operation mult = new Operation("_ * _", a2, floatSort, modName);
	    mult.setAssociativity();
	    mult.setPriority(30);
	    mult.setInfo("system-default");
	    result.addOperation(mult);

	    Operation div = new Operation("_ / _", a2, floatSort, modName);
	    div.setAssociativity();
	    div.setPriority(30);
	    div.setInfo("system-default");
	    result.addOperation(div);
	    
	    Operation less = new Operation("_ < _", a2, bool, modName);
	    less.setInfo("system-default");
	    result.addOperation(less);

	    Operation leq = new Operation("_ <= _", a2, bool, modName);
	    leq.setInfo("system-default");
	    result.addOperation(leq);

	    Operation great = new Operation("_ > _", a2, bool, modName);
	    great.setInfo("system-default");
	    result.addOperation(great);

	    Operation egr = new Operation("_ >= _", a2, bool, modName);
	    egr.setInfo("system-default");
	    result.addOperation(egr);
	    
            Operation exp  = new Operation("exp", a1, floatSort, modName);
	    exp.setInfo("system-default");
	    result.addOperation(exp);
	    
	    Operation log  = new Operation("log", a1, floatSort, modName);
	    log.setInfo("system-default");
	    result.addOperation(log);
	    
	    Operation sqrt = new Operation("sqrt", a1, floatSort, modName);
	    sqrt.setInfo("system-default");
	    result.addOperation(sqrt);
	    
	    Operation abs  = new Operation("abs", a1, floatSort, modName);
	    abs.setInfo("system-default");
	    result.addOperation(abs);
	    
	    Operation sin  = new Operation("sin", a1, floatSort, modName);
	    sin.setInfo("system-default");
	    result.addOperation(sin);
	    
	    Operation cos  = new Operation("cos", a1, floatSort, modName);
	    cos.setInfo("system-default");
	    result.addOperation(cos);
	    
	    Operation atan = new Operation("atan", a1, floatSort, modName);
	    atan.setInfo("system-default");
	    result.addOperation(atan);
	    
	    Operation pi   = new Operation("pi", floatSort, modName);
	    pi.setInfo("system-default");
	    result.addOperation(pi);

	    Operation sub1 = new Operation("- _", a1, floatSort, modName);
	    sub1.setPriority(20);
	    sub1.setInfo("system-default");
	    result.addOperation(sub1);

	    result.protectedImport(createInt());
            Sort inte = (Sort)result.sorts.elementAt(3);
            result.addSubsort(floatSort, inte);	    

	} catch (Exception e) {
	    e.printStackTrace();
	    
	}
	return result;     
	
    }
    

    public static void main(String args[]) {
	System.out.println(createFloat());
    }

}










package ch.ethz.sae;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Manager;
import apron.Polka;
import apron.Texpr1Intern;
import apron.Texpr1VarNode;
import soot.IntegerType;
import soot.Local;
import soot.SootClass;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;
import soot.jimple.internal.AbstractJimpleFloatBinopExpr;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;
import soot.util.Chain;

// Implement your numerical analysis here.
public class Analysis extends ForwardBranchedFlowAnalysis<AWrapper> {

	private static final int WIDENING_THRESHOLD = 6;

	private HashMap<Unit, Counter> loopHeads, backJumps;

	private void recordIntLocalVars() {

		Chain<Local> locals = g.getBody().getLocals();

		int count = 0;
		Iterator<Local> it = locals.iterator();
		while (it.hasNext()) {
			JimpleLocal next = (JimpleLocal) it.next();
			if (next.getType() instanceof IntegerType)
				count += 1;
		}

		local_ints = new String[count];

		int i = 0;
		it = locals.iterator();
		while (it.hasNext()) {
			JimpleLocal next = (JimpleLocal) it.next();
			String name = next.getName();
			if (next.getType() instanceof IntegerType)
				local_ints[i++] = name;
		}
	}

	private void recordIntClassVars() {

		Chain<SootField> ifields = jclass.getFields();

		int count = 0;
		Iterator<SootField> it = ifields.iterator();
		while (it.hasNext()) {
			SootField next = it.next();
			if (next.getType() instanceof IntegerType)
				count += 1;
		}

		class_ints = new String[count];

		int i = 0;
		it = ifields.iterator();
		while (it.hasNext()) {
			SootField next = it.next();
			String name = next.getName();
			if (next.getType() instanceof IntegerType)
				class_ints[i++] = name;
		}
	}

	/* Builds an environment with integer variables. */
	public void buildEnvironment() {

		recordIntLocalVars();
		recordIntClassVars();

		String ints[] = new String[local_ints.length + class_ints.length];

		/* add local ints */
		for (int i = 0; i < local_ints.length; i++) {
			ints[i] = local_ints[i];
		}

		/* add class ints */
		for (int i = 0; i < class_ints.length; i++) {
			ints[local_ints.length + i] = class_ints[i];
		}

		env = new Environment(ints, reals);
	}

	/* Instantiate a domain. */
	private void instantiateDomain() {
		man = new Polka(true);
	}

	/* === Constructor === */
	public Analysis(UnitGraph g, SootClass jc) {
		super(g);

		this.g = g;
		this.jclass = jc;

		buildEnvironment();
		instantiateDomain();

		loopHeads = new HashMap<Unit, Counter>();
		backJumps = new HashMap<Unit, Counter>();
		for (Loop l : new LoopNestTree(g.getBody())) {
			loopHeads.put(l.getHead(), new Counter(0));
			backJumps.put(l.getBackJumpStmt(), new Counter(0));
		}
	}

	void run() {
		doAnalysis();
	}

	@Override
	protected void flowThrough(AWrapper inWrapper, Unit op,
			List<AWrapper> fallOutWrappers /*if continues at next statement?*/
			, List<AWrapper> branchOutWrappers/*if doesnt continue at following statement?*/) {
		/*meetCopy(Manager man, Tcons1 c)
		Returns a new
 		abstract element that contains (an over-approximation of)
  		the set-intersection of this with the constraint in c.*/
		
		/* A Tcons1 represents a constraint over variables denoted
		   by name in an environment.
		 	A Tcons1 is implemented as a pair containing a Tcons0 and
 			an Environment, manipulated in conjunction. Direct access 
 		to the fields is prohibited, to avoid desynchronizing them.*/
		
		//use MpqScalar as constants

		Stmt s = (Stmt) op;

		if (s instanceof DefinitionStmt) {
			DefinitionStmt sd = (DefinitionStmt) s;
			Value lhs = sd.getLeftOp();
			Value rhs = sd.getRightOp();
			/* TODO: handle assignment */
			if (rhs instanceof JMulExpr) {
				//modify the AWrapper stuff
				
				//make an apron Variable from lhs, for leftMember = lhs-rhs
				if (lhs instanceof JimpleLocal){
					Texpr1VarNode leftVariable = Texpr1VarNode(( (JimpleLocal) lhs).getName());
				}
				//build rhs expression with apron Texpr1BinNode
				Value op1 = ((JMulExpr) rhs).getOp1();
				Value op2 = ((JMulExpr) rhs).getOp2();
				
				if (isIntValue(op1)){
					
				}else{
					
				}
				//build leftMember for Tcons1
				Texpr1BinNode(int o, Texpr1Node lAr, Texpr1Node rAr);
				//lhs - rhs
				/* Texpr1Intern objects can be converted from and to
				*Texpr1Node concrete expression trees for construction and inspection.*/
				Texpr1Intern leftMember = 
				//build constraint with apron Tcons1

				Tcons1 constraint = Tcons1(0, leftMember); //0 for EQ
				
				//add constraint to branchOutWrappers
				
			}else if(rhs instanceof JSubExpr) {
				//modify the AWrapper stuff
				
			}else if(rhs instanceof JAddExpr) {
				//modify the AWrapper stuff
				
			}else{
				//go to top or whatever. Do we have to handle this case?
			}
			

		} else if (s instanceof JIfStmt) {
			IfStmt ifStmt = (JIfStmt) s;
			/* TODO: handle if statement*/
			Value cond = ifStmt.getCondition();
			if (cond instanceof JEqExpr) {
				//modify the AWrapper stuff
				//build expression with apron Texpr1BinNode
				
				//build constraint with apron Tcons1
				
				/*add constraint to fallOutWrappers or branchOutWrappers
				 *depending on whether cond is false or true*/
				
				
			}else if(cond instanceof JGeExpr){
				//modify the AWrapper stuff
				
			}else if(cond instanceof JGtExpr){
				//modify the AWrapper stuff
				
			}else if(cond instanceof JLeExpr){
				//modify the AWrapper stuff
				
			}else if(cond instanceof JLtExpr){
				//modify the AWrapper stuff
				
			}else if(cond instanceof JNeExpr){
				//modify the AWrapper stuff
				
			}else{
				//got to top or whatever. Do we have to handle this case?
			}
		} else {
			//go to top? or give some other function for loops?
		}
	}

	@Override
	protected void copy(AWrapper source, AWrapper dest) {
		try {
			dest.set(new Abstract1(man, source.get()));
		} catch (ApronException e) {
			e.printStackTrace();
		}
	}

	@Override
	protected AWrapper entryInitialFlow() {
		//can change the result if needed?
		Abstract1 top = null;
		try {
			top = new Abstract1(man, env);
		} catch (ApronException e) {
		}
		return new AWrapper(top);
	}

	private static class Counter {
		int value;

		Counter(int v) {
			value = v;
		}
	}

	@Override
	protected void merge(Unit succNode, AWrapper w1, AWrapper w2, AWrapper w3) {
		Counter count = loopHeads.get(succNode);

		Abstract1 a1 = w1.get();
		Abstract1 a2 = w2.get();
		Abstract1 a3 = null;

		try {
			if (count != null) {
				++count.value;
				if (count.value < WIDENING_THRESHOLD) {
					a3 = a1.joinCopy(man, a2);
				} else {
					a3 = a1.widening(man, a2);
				}
			} else {
				a3 = a1.joinCopy(man, a2);
			}
			w3.set(a3);
		} catch (Exception e) {
			System.out.println(e);
		}
	}

	@Override
	protected void merge(AWrapper src1, AWrapper src2, AWrapper trg) {

		Abstract1 a1 = src1.get();
		Abstract1 a2 = src2.get();
		Abstract1 a3 = null;

		try {
			a3 = a1.joinCopy(man, a2);
		} catch (ApronException e) {
			e.printStackTrace();
		}
		trg.set(a3);
	}

	@Override
	protected AWrapper newInitialFlow() {
		Abstract1 bot = null;

		try {
			bot = new Abstract1(man, env, true);
		} catch (ApronException e) {
		}
		AWrapper a = new AWrapper(bot);
		a.man = man;
		return a;

	}

	public static final boolean isIntValue(Value val) {
		return val.getType().toString().equals("int")
				|| val.getType().toString().equals("short")
				|| val.getType().toString().equals("byte");
	}


	public static Manager man;
	public static Environment env;
	public UnitGraph g;
	public String local_ints[]; // integer local variables of the method
	public static String reals[] = { "x" };
	public SootClass jclass;
	private String class_ints[]; // integer class variables where the method is
	// defined
}

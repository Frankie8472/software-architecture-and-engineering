package ch.ethz.sae;

import java.lang.Integer;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import apron.*;

import soot.*;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.Stmt;
import soot.jimple.internal.*;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;
import soot.util.Chain;

// Implement your numerical analysis here.
public class Analysis extends ForwardBranchedFlowAnalysis<AWrapper> {

	private static final int WIDENING_THRESHOLD = 6;

	private HashMap<Unit, Counter> loopHeads, backJumps;

	public static Manager man;
	public static Environment env;
	public UnitGraph g;
	public String local_ints[]; // integer local variables of the method
	public static String reals[] = { "x" };
	public SootClass jclass;
	private String class_ints[]; // integer class variables where the method is defined

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
			List<AWrapper> fallOutWrappers, List<AWrapper> branchOutWrappers) {

		Stmt s = (Stmt) op;

		// Handle definition statement
		if (s instanceof DefinitionStmt) {
			DefinitionStmt sd = (DefinitionStmt) s;
			Value lhs = sd.getLeftOp();
			Value rhs = sd.getRightOp();

			// Handle left side of expr
            Texpr1Node ApronLhs = null;
			if (lhs instanceof JimpleLocal){
				ApronLhs = new Texpr1VarNode(lhs.toString());
			} else {
                System.err.println("Left side is no instance of JimpleLocal");
            }

			// Handle right side of expr
                // Handle multiplication expr
            if (rhs instanceof JMulExpr) {
                Value op1 = ((JMulExpr) rhs).getOp1();
                Value op2 = ((JMulExpr) rhs).getOp2();
                Texpr1Node lArg = null;
                Texpr1Node rArg = null;
                if (op1 instanceof IntConstant){
                    lArg = new Texpr1CstNode(new MpqScalar(Integer.parseInt(op1.toString())));
                } else if (op1 instanceof JimpleLocal){
                    lArg = new Texpr1VarNode(op1.toString());

                } else {
                    System.out.print("op1 is instance of unknown");
                }

                if (op2 instanceof IntConstant){
                    rArg = new Texpr1CstNode(new MpqScalar(Integer.parseInt(op2.toString())));
                } else if (op1 instanceof JimpleLocal){
                    rArg = new Texpr1VarNode(op2.toString());

                } else {
                    System.out.print("op2 is instance of unknown");
                }
                if (lArg != null && rArg != null && ApronLhs != null) {
                    Texpr1BinNode ApronRhs = new Texpr1BinNode(Texpr1BinNode.OP_MUL, lArg, rArg);
                    Texpr1BinNode ApronRhs2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Tcons1 constraint = new Tcons1(Tcons1.EQ, new Texpr1Intern(env, ApronRhs2zero));

                    try {
                        fallOutWrappers.get(0).set(inWrapper.get().meetCopy(man, constraint));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }

			} else if (rhs instanceof JAddExpr) {        // Handle addition expr
                Value op1 = ((JAddExpr) rhs).getOp1();
                Value op2 = ((JAddExpr) rhs).getOp2();
                Texpr1Node lArg = null;
                Texpr1Node rArg = null;
                if (op1 instanceof IntConstant){
                    lArg = new Texpr1CstNode(new MpqScalar(Integer.parseInt(op1.toString())));
                } else if (op1 instanceof JimpleLocal){
                    lArg = new Texpr1VarNode(op1.toString());

                } else {
                    System.out.print("op1 is instance of unknown");
                }

                if (op2 instanceof IntConstant){
                    rArg = new Texpr1CstNode(new MpqScalar(Integer.parseInt(op2.toString())));
                } else if (op1 instanceof JimpleLocal){
                    rArg = new Texpr1VarNode(op2.toString());

                } else {
                    //System.out.print("op2 is instance of unknown");
                }
                if (lArg != null && rArg != null && ApronLhs != null) {
                    Texpr1BinNode ApronRhs = new Texpr1BinNode(Texpr1BinNode.OP_ADD, lArg, rArg);
                    Texpr1BinNode ApronRhs2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Tcons1 constraint = new Tcons1(Tcons1.EQ, new Texpr1Intern(env, ApronRhs2zero));

                    try {
                        fallOutWrappers.get(0).set(inWrapper.get().meetCopy(man, constraint));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }

			} else if (rhs instanceof JSubExpr){         // Handle subtraction expr
                Value op1 = ((JSubExpr) rhs).getOp1();
                Value op2 = ((JSubExpr) rhs).getOp2();
                Texpr1Node lArg = null;
                Texpr1Node rArg = null;
                if (op1 instanceof IntConstant){
                    lArg = new Texpr1CstNode(new MpqScalar(Integer.parseInt(op1.toString())));
                } else if (op1 instanceof JimpleLocal){
                    lArg = new Texpr1VarNode(op1.toString());

                } else {
                    System.out.print("op1 is instance of unknown");
                }

                if (op2 instanceof IntConstant){
                    rArg = new Texpr1CstNode(new MpqScalar(Integer.parseInt(op2.toString())));
                } else if (op1 instanceof JimpleLocal){
                    rArg = new Texpr1VarNode(op2.toString());

                } else {
                    System.out.print("op2 is instance of unknown");
                }
                if (lArg != null && rArg != null && ApronLhs != null) {
                    Texpr1BinNode ApronRhs = new Texpr1BinNode(Texpr1BinNode.OP_SUB, lArg, rArg);
                    Texpr1BinNode ApronRhs2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Tcons1 constraint = new Tcons1(Tcons1.EQ, new Texpr1Intern(env, ApronRhs2zero));
                    try {
                        fallOutWrappers.get(0).set(inWrapper.get().meetCopy(man, constraint));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }
			} else {
				//System.err.println("Right side is instance of unknown");
			}

		// Handle if statement
        } else if (s instanceof JIfStmt) {
			IfStmt ifStmt = (JIfStmt) s;
			Value cond = ifStmt.getCondition();
            if (cond instanceof JEqExpr){           // Handle ==
                Value lhs = ((JEqExpr) cond).getOp1();
                Value rhs = ((JEqExpr) cond).getOp2();
                Texpr1Node ApronLhs = null;
                Texpr1Node ApronRhs = null;

                if (lhs instanceof JimpleLocal){
                    ApronLhs = new Texpr1VarNode(lhs.toString());
                } else if (lhs instanceof IntConstant){
                    ApronLhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(lhs.toString())));

                } else {
                    System.err.println("lhs is instance of unknown");
                }

                if (rhs instanceof JimpleLocal){
                    ApronRhs = new Texpr1VarNode(rhs.toString());
                } else if (rhs instanceof IntConstant){
                    ApronRhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(rhs.toString())));
                } else {
                    System.err.println("rhs is instance of unknown");
                }

                if (ApronLhs != null && ApronRhs != null){
                    Texpr1BinNode Apron2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Texpr1BinNode ApronInvert = new Texpr1BinNode(Texpr1BinNode.OP_SUB, new Texpr1CstNode(), Apron2zero);
                    Tcons1 branchOutConstraint = new Tcons1(Tcons1.EQ, new Texpr1Intern(env, Apron2zero));
                    Tcons1 fallOutConstraint = new Tcons1(Tcons1.EQ, new Texpr1Intern(env, ApronInvert));
                    try {
                        fallOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, fallOutConstraint)));
                        branchOutWrappers.set(0,  new AWrapper(inWrapper.get().meetCopy(man, branchOutConstraint)));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }

            } else if (cond instanceof JGeExpr){    // Handle >=
                Value lhs = ((JGeExpr) cond).getOp1();
                Value rhs = ((JGeExpr) cond).getOp2();
                Texpr1Node ApronLhs = null;
                Texpr1Node ApronRhs = null;

                if (lhs instanceof JimpleLocal){
                    ApronLhs = new Texpr1VarNode(lhs.toString());
                } else if (lhs instanceof IntConstant){
                    ApronLhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(lhs.toString())));

                } else {
                    System.err.println("lhs is instance of unknown");
                }

                if (rhs instanceof JimpleLocal){
                    ApronRhs = new Texpr1VarNode(rhs.toString());
                } else if (rhs instanceof IntConstant){
                    ApronRhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(rhs.toString())));
                } else {
                    System.err.println("rhs is instance of unknown");
                }

                if (ApronLhs != null && ApronRhs != null){
                    Texpr1BinNode Apron2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronLhs, ApronRhs);
                    Texpr1BinNode ApronInvert = new Texpr1BinNode(Texpr1BinNode.OP_SUB, new Texpr1CstNode(), Apron2zero);
                    Tcons1 branchOutConstraint = new Tcons1(Tcons1.SUPEQ, new Texpr1Intern(env, Apron2zero));
                    Tcons1 fallOutConstraint = new Tcons1(Tcons1.SUPEQ, new Texpr1Intern(env, ApronInvert));
                    try {
                        fallOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, fallOutConstraint)));
                        branchOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, branchOutConstraint)));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }

            } else if (cond instanceof JGtExpr) {   // Handle >
                Value lhs = ((JGtExpr) cond).getOp1();
                Value rhs = ((JGtExpr) cond).getOp2();
                Texpr1Node ApronLhs = null;
                Texpr1Node ApronRhs = null;

                if (lhs instanceof JimpleLocal){
                    ApronLhs = new Texpr1VarNode(lhs.toString());
                } else if (lhs instanceof IntConstant){
                    ApronLhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(lhs.toString())));

                } else {
                    System.err.println("lhs is instance of unknown");
                }

                if (rhs instanceof JimpleLocal){
                    ApronRhs = new Texpr1VarNode(rhs.toString());
                } else if (rhs instanceof IntConstant){
                    ApronRhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(rhs.toString())));
                } else {
                    System.err.println("rhs is instance of unknown");
                }

                if (ApronLhs != null && ApronRhs != null){
                    Texpr1BinNode Apron2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronLhs, ApronRhs);
                    Texpr1BinNode ApronInvert = new Texpr1BinNode(Texpr1BinNode.OP_SUB, new Texpr1CstNode(), Apron2zero);
                    Tcons1 branchOutConstraint = new Tcons1(Tcons1.SUP, new Texpr1Intern(env, Apron2zero));
                    Tcons1 fallOutConstraint = new Tcons1(Tcons1.SUP, new Texpr1Intern(env, ApronInvert));
                    try {
                        fallOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, fallOutConstraint)));
                        branchOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, branchOutConstraint)));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }

            } else if (cond instanceof JLeExpr){    // Handle <=
                Value lhs = ((JLeExpr) cond).getOp1();
                Value rhs = ((JLeExpr) cond).getOp2();
                Texpr1Node ApronLhs = null;
                Texpr1Node ApronRhs = null;

                if (lhs instanceof JimpleLocal){
                    ApronLhs = new Texpr1VarNode(lhs.toString());
                } else if (lhs instanceof IntConstant){
                    ApronLhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(lhs.toString())));

                } else {
                    System.err.println("lhs is instance of unknown");
                }

                if (rhs instanceof JimpleLocal){
                    ApronRhs = new Texpr1VarNode(rhs.toString());
                } else if (rhs instanceof IntConstant){
                    ApronRhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(rhs.toString())));
                } else {
                    System.err.println("rhs is instance of unknown");
                }

                if (ApronLhs != null && ApronRhs != null){
                    Texpr1BinNode Apron2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Texpr1BinNode ApronInvert = new Texpr1BinNode(Texpr1BinNode.OP_SUB, new Texpr1CstNode(), Apron2zero);
                    Tcons1 branchOutConstraint = new Tcons1(Tcons1.SUPEQ, new Texpr1Intern(env, Apron2zero));
                    Tcons1 fallOutConstraint = new Tcons1(Tcons1.SUPEQ, new Texpr1Intern(env, ApronInvert));
                    try {
                        fallOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, fallOutConstraint)));
                        branchOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, branchOutConstraint)));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }

            } else if (cond instanceof JLtExpr){    // Handle <
                Value lhs = ((JLtExpr) cond).getOp1();
                Value rhs = ((JLtExpr) cond).getOp2();
                Texpr1Node ApronLhs = null;
                Texpr1Node ApronRhs = null;

                if (lhs instanceof JimpleLocal){
                    ApronLhs = new Texpr1VarNode(lhs.toString());
                } else if (lhs instanceof IntConstant){
                    ApronLhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(lhs.toString())));

                } else {
                    System.err.println("lhs is instance of unknown");
                }

                if (rhs instanceof JimpleLocal){
                    ApronRhs = new Texpr1VarNode(rhs.toString());
                } else if (rhs instanceof IntConstant){
                    ApronRhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(rhs.toString())));
                } else {
                    System.err.println("rhs is instance of unknown");
                }

                if (ApronLhs != null && ApronRhs != null){
                    Texpr1BinNode Apron2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Texpr1BinNode ApronInvert = new Texpr1BinNode(Texpr1BinNode.OP_SUB, new Texpr1CstNode(), Apron2zero);
                    Tcons1 branchOutConstraint = new Tcons1(Tcons1.SUP, new Texpr1Intern(env, Apron2zero));
                    Tcons1 fallOutConstraint = new Tcons1(Tcons1.SUP, new Texpr1Intern(env, ApronInvert));
                    try {
                        fallOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, fallOutConstraint)));
                        branchOutWrappers.set(0,  new AWrapper(inWrapper.get().meetCopy(man, branchOutConstraint)));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }
            } else if (cond instanceof JNeExpr){    // Handle !=
                Value lhs = ((JNeExpr) cond).getOp1();
                Value rhs = ((JNeExpr) cond).getOp2();
                Texpr1Node ApronLhs = null;
                Texpr1Node ApronRhs = null;

                if (lhs instanceof JimpleLocal){
                    ApronLhs = new Texpr1VarNode(lhs.toString());
                } else if (lhs instanceof IntConstant){
                    ApronLhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(lhs.toString())));

                } else {
                    System.err.println("lhs is instance of unknown");
                }

                if (rhs instanceof JimpleLocal){
                    ApronRhs = new Texpr1VarNode(rhs.toString());
                } else if (rhs instanceof IntConstant){
                    ApronRhs = new Texpr1CstNode(new MpqScalar(Integer.parseInt(rhs.toString())));
                } else {
                    System.err.println("rhs is instance of unknown");
                }

                if (ApronLhs != null && ApronRhs != null){
                    Tcons1[] fallOutConstraints = new Tcons1[2];
                    Texpr1BinNode Apron2zero = new Texpr1BinNode(Texpr1BinNode.OP_SUB, ApronRhs, ApronLhs);
                    Texpr1BinNode ApronInvert = new Texpr1BinNode(Texpr1BinNode.OP_SUB, new Texpr1CstNode(), Apron2zero);
                    Tcons1 branchOutConstraint = new Tcons1(Tcons1.EQ, new Texpr1Intern(env, Apron2zero));
                    fallOutConstraints[0] = new Tcons1(Tcons1.SUP, new Texpr1Intern(env, Apron2zero));
                    fallOutConstraints[1] = new Tcons1(Tcons1.SUP, new Texpr1Intern(env, ApronInvert));
                    try {
                        fallOutWrappers.set(0, new AWrapper(inWrapper.get().meetCopy(man, fallOutConstraints)));
                        branchOutWrappers.set(0,  new AWrapper(inWrapper.get().meetCopy(man, branchOutConstraint)));
                    } catch (ApronException e) {
                        e.printStackTrace();
                    }
                }
            } else {
                System.err.println("Cond is instance of unknown");
            }

		} else {
            //System.err.println("s is instance of unknown");
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
}

package rs.ac.bg.etf.pp1;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;

import rs.ac.bg.etf.pp1.ast.AddOp;
import rs.ac.bg.etf.pp1.ast.AddopsExpr;
import rs.ac.bg.etf.pp1.ast.BeforeCond;
import rs.ac.bg.etf.pp1.ast.BeforeElse;
import rs.ac.bg.etf.pp1.ast.BeforeFor;
import rs.ac.bg.etf.pp1.ast.BeforeIf;
import rs.ac.bg.etf.pp1.ast.BeforeThen;
import rs.ac.bg.etf.pp1.ast.CondAnd;
import rs.ac.bg.etf.pp1.ast.CondFactFor;
import rs.ac.bg.etf.pp1.ast.CondOr;
import rs.ac.bg.etf.pp1.ast.CondRelops;
import rs.ac.bg.etf.pp1.ast.Design;
import rs.ac.bg.etf.pp1.ast.DesignArrayAccess;
import rs.ac.bg.etf.pp1.ast.DesignAssignment;
import rs.ac.bg.etf.pp1.ast.DesignDec;
import rs.ac.bg.etf.pp1.ast.DesignFieldAccess;
import rs.ac.bg.etf.pp1.ast.DesignIdent;
import rs.ac.bg.etf.pp1.ast.DesignIdentNamespace;
import rs.ac.bg.etf.pp1.ast.DesignInc;
import rs.ac.bg.etf.pp1.ast.DesignMethCall;
import rs.ac.bg.etf.pp1.ast.DesignMultiAssignment;
import rs.ac.bg.etf.pp1.ast.DesignsListDesign;
import rs.ac.bg.etf.pp1.ast.DesignsListFirstDesign;
import rs.ac.bg.etf.pp1.ast.DesignsListNoDesign;
import rs.ac.bg.etf.pp1.ast.DivOp;
import rs.ac.bg.etf.pp1.ast.EqualOp;
import rs.ac.bg.etf.pp1.ast.FactorConst;
import rs.ac.bg.etf.pp1.ast.FactorDesign;
import rs.ac.bg.etf.pp1.ast.FactorDesignFCall;
import rs.ac.bg.etf.pp1.ast.FactorNewArrRef;
import rs.ac.bg.etf.pp1.ast.GreaterEqualOp;
import rs.ac.bg.etf.pp1.ast.GreaterOp;
import rs.ac.bg.etf.pp1.ast.LessEqualOp;
import rs.ac.bg.etf.pp1.ast.LessOp;
import rs.ac.bg.etf.pp1.ast.LoopStart;
import rs.ac.bg.etf.pp1.ast.MethDecl;
import rs.ac.bg.etf.pp1.ast.MethName;
import rs.ac.bg.etf.pp1.ast.MulOp;
import rs.ac.bg.etf.pp1.ast.MulopsTerm;
import rs.ac.bg.etf.pp1.ast.NoAddopsExprNeg;
import rs.ac.bg.etf.pp1.ast.NoCondAnd;
import rs.ac.bg.etf.pp1.ast.NoCondFor;
import rs.ac.bg.etf.pp1.ast.NoCondOr;
import rs.ac.bg.etf.pp1.ast.NoCondRelops;
import rs.ac.bg.etf.pp1.ast.NoDesignsList;
import rs.ac.bg.etf.pp1.ast.NoPrintExtraArgs;
import rs.ac.bg.etf.pp1.ast.NotEqualOp;
import rs.ac.bg.etf.pp1.ast.PrintExtraArg;
import rs.ac.bg.etf.pp1.ast.StmntBreak;
import rs.ac.bg.etf.pp1.ast.StmntContinue;
import rs.ac.bg.etf.pp1.ast.StmntForCond;
import rs.ac.bg.etf.pp1.ast.StmntIfElse;
import rs.ac.bg.etf.pp1.ast.StmntPrint;
import rs.ac.bg.etf.pp1.ast.StmntRead;
import rs.ac.bg.etf.pp1.ast.StmntRetExpr;
import rs.ac.bg.etf.pp1.ast.StmntRetVoid;
import rs.ac.bg.etf.pp1.ast.SyntaxNode;
import rs.ac.bg.etf.pp1.ast.VisitorAdaptor;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class CodeGenerator extends VisitorAdaptor {
	
	private ArrayDeque<List<List<Integer>>> patchesIf = new ArrayDeque<>();
	private ArrayDeque<List<List<Integer>>> patchesFor = new ArrayDeque<>();
	private List<Obj> arrayAssignDests= new ArrayList<>();
	private int condLevels = 4;

	//=================================================================================
	// Helpers
	private Boolean putDesignToCode(Design design) {
		Class<? extends SyntaxNode> parentClass = design.getParent().getClass();
		if (
		parentClass.equals(DesignArrayAccess.class)
		|| parentClass.equals(DesignMethCall.class)
		|| parentClass.equals(DesignInc.class)
		|| parentClass.equals(DesignDec.class)
		|| parentClass.equals(FactorDesign.class)
		|| parentClass.equals(DesignFieldAccess.class)
		) {
			return true;
		}
//		if (parentClass.equals(DesignMultiAssignment.class)) {
//			if (((DesignMultiAssignment) design.getParent()).getDesign1().equals(design)) { //valjda???
//				return true;
//			}
//		}
		return false;
	}
	
	//=================================================================================
	// MethName ::=
	@Override
	public void visit(MethName methName) {
		if("main".equalsIgnoreCase(methName.getMethName())){
			Code.mainPc = Code.pc;
		}
		methName.obj.setAdr(Code.pc);
		// Generate the entry
		Code.put(Code.enter);
		Code.put(methName.obj.getLevel());
		Code.put(methName.obj.getLocalSymbols().size());
	}
	//=================================================================================
	// MethodDecl ::=
	@Override
	public void visit(MethDecl methDecl) {
		if (methDecl.obj.getType().equals(Tab.noType)) {
			Code.put(Code.exit);
			Code.put(Code.return_);
			return;
		}
		String errorMsg = "Route has no return value!"; // Comment if too big for buffer
		for (char c : errorMsg.toCharArray()) {
			Code.loadConst(c);
			Code.loadConst(1);
			Code.put(Code.bprint);
		}
		Code.put(Code.trap);
		Code.put(1);
	}
	//=================================================================================
	// PrintExtraArgs ::=
	public void visit(PrintExtraArg printExtraArg){
		Code.loadConst(printExtraArg.getNumConst());
	}
	
	public void visit(NoPrintExtraArgs noPrintExtraArgs){
		StmntPrint stmntPrint = (StmntPrint)(noPrintExtraArgs.getParent());
		if(stmntPrint.getExpr().struct.equals(Tab.intType)){
			Code.loadConst(5);
		}
		else {
			Code.loadConst(1);
		}
	}
	//=================================================================================
	// Statement ::= (A lvl)
	public void visit(StmntPrint stmntPrint){
		if(stmntPrint.getExpr().struct.equals(Tab.intType)){
			//Code.loadConst(5); done in PrintExtraArgs 
			Code.put(Code.print);
		}
		else if(stmntPrint.getExpr().struct.equals(SemanticAnalyzer.boolType)){
			//Code.loadConst(1); done in PrintExtraArgs 
			Code.put(Code.print);
		}
		else {
			//Code.loadConst(1);  done in PrintExtraArgs 
			Code.put(Code.bprint);
		}
	}
	
	@Override
	public void visit(StmntRead stmntRead) {
		Obj dst = stmntRead.getDesign().obj;
		if (dst.getType().equals(Tab.charType)) {
			Code.put(Code.bread);
		} else {
			Code.put(Code.read);
		}
		Code.store(dst);
	}
	
	@Override
	public void visit(StmntRetVoid stmntRetVoid) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(StmntRetExpr stmntRetExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	@Override
	public void visit(StmntIfElse stmntIfElse) {
		for (Integer i : patchesIf.peek().get(3)) {
			Code.fixup(i);
		}
		patchesIf.peek().get(3).clear();
		patchesIf.pop();
	}
	
	@Override
	public void visit(BeforeIf beforeIf) {
		List<List<Integer>> newIfElseBlock = new ArrayList<>();
		for (int i = 0; i < condLevels; ++i)
			newIfElseBlock.add(new ArrayList<Integer>());
		patchesIf.push(newIfElseBlock);
	}
	
	@Override
	public void visit(BeforeThen beforeThen) {
		Code.putJump(0); // condition incorrect -> jump to adr(else)
		patchesIf.peek().get(2).add(Code.pc - 2);
		for (Integer i : patchesIf.peek().get(1)) {
			Code.fixup(i);
		}
		patchesIf.peek().get(1).clear();
	}
	
	@Override
	public void visit(BeforeElse beforeElse) {
		Code.putJump(0); //then branch happened -> jump to adr(after if)
		patchesIf.peek().get(3).add(Code.pc - 2);
		for (Integer i : patchesIf.peek().get(2)) {
			Code.fixup(i);
		}
		patchesIf.peek().get(2).clear();
	}

	@Override
	public void visit(StmntForCond stmntForCond) {
		for (Integer i : patchesFor.peek().get(2)) {
			Code.putJump(i); //loop back to (;;here)
		}
		patchesFor.peek().get(2).clear();
		for (Integer i : patchesFor.peek().get(0)) {
			Code.fixup(i);
		}
		patchesFor.peek().get(0).clear();
		patchesFor.pop();
	}
	
	@Override
	public void visit(BeforeFor beforeFor) {
		List<List<Integer>> newForBlock = new ArrayList<>();
		for (int i = 0; i < condLevels; ++i)
			newForBlock.add(new ArrayList<Integer>());
		patchesFor.push(newForBlock);
	}
	
	@Override
	public void visit(BeforeCond beforeCond) {
		patchesFor.peek().get(3).add(Code.pc); // jump here to check if new loop(;here;)
	}
	
	@Override
	public void visit(NoCondFor noCondFor) {
		Code.putJump(0); // jump to loop start
		patchesFor.peek().get(1).add(Code.pc-2);
		patchesFor.peek().get(2).add(Code.pc); // jump here to do the after loop statements(;;here)
	}
	
	@Override
	public void visit(CondFactFor condFactFor) {
		Code.putJump(0); // jump to loop start
		patchesFor.peek().get(1).add(Code.pc-2);
		patchesFor.peek().get(2).add(Code.pc); // jump here to do the after loop statements(;;here)
	}
	
	@Override
	public void visit(LoopStart loopStart) {
		for (Integer i : patchesFor.peek().get(3)) {
			Code.putJump(i); // jump to before cond to check
		}
		patchesFor.peek().get(3).clear();
		for (Integer i : patchesFor.peek().get(1)) { 
			Code.fixup(i); // jump here to start loop statements(;;)here
		}
		patchesFor.peek().get(1).clear();
	}
	
	@Override
	public void visit(StmntBreak stmntBreak) {
		Code.putJump(0); // jump to loop start
		patchesFor.peek().get(0).add(Code.pc-2);
	}
	
	@Override
	public void visit(StmntContinue stmntContinue) {
		for (Integer i : patchesFor.peek().get(2)) {
			Code.putJump(i); //loop back to (;;here)
		}
	}
	//=================================================================================
	// Design (lvl B) ::=
	@Override
	public void visit(DesignIdentNamespace designIdentNamespace) {
		if (putDesignToCode(designIdentNamespace)) {
			Code.load(designIdentNamespace.obj);
		}
	}
	
	@Override
	public void visit(DesignIdent designIdent) {
		if (putDesignToCode(designIdent)) {
			Code.load(designIdent.obj);
		}
	}
	
	@Override
	public void visit(DesignArrayAccess designArrayAccess) {
		if (putDesignToCode(designArrayAccess)) {
			Code.load(designArrayAccess.obj);
		}
	}
	//=================================================================================
	// Factor (lvl A) ::=
	@Override
	public void visit(FactorConst factorConst){
		Code.load(factorConst.getConstValue().obj);
	}
	
	@Override
	public void visit(FactorNewArrRef factorNewArrRef) {
		Struct typeToAllocate = factorNewArrRef.struct.getElemType();
		Code.put(Code.newarray);
		Code.put(typeToAllocate.equals(Tab.charType) ? 0 : 1);
	}
	
	@Override
	public void visit(FactorDesignFCall factorDesignFCall) {
		Obj methodObj = factorDesignFCall.getDesign().obj;
		int offset = methodObj.getAdr() - Code.pc;
		// Parameters from Expr already on stack
		Code.put(Code.call);
		Code.put2(offset);
	}
	//=================================================================================
	// Term ::=

	@Override
	public void visit(MulopsTerm mulopsTerm) {
		if (mulopsTerm.getMulops().getClass().equals(MulOp.class)) {
			Code.put(Code.mul);
		}
		else if (mulopsTerm.getMulops().getClass().equals(DivOp.class)) {
			Code.put(Code.div);
		}
		else {
			Code.put(Code.rem);
		}
	}
	//=================================================================================
	// Expr ::=
	@Override
	public void visit(AddopsExpr addopsExpr) {
		if (addopsExpr.getAddops().getClass().equals(AddOp.class)) {
			Code.put(Code.add);
		}
		else {
			Code.put(Code.sub);
		}
	}

	@Override
	public void visit(NoAddopsExprNeg noAddopsExprNeg) {
		Code.put(Code.neg);
	}
	//=================================================================================
	// CondFact ::=		
	@Override
	public void visit(NoCondRelops noCondRelops) {
		Code.loadConst(1);
		Code.putFalseJump(Code.eq, 0); //one condfact is false -> condterm is false -> jump to adr(after condterm)
		if (noCondRelops.getParent().getClass().equals(CondFactFor.class)) {
			patchesFor.peek().get(0).add(Code.pc-2);
		}
		else {
			patchesIf.peek().get(0).add(Code.pc-2);
		}
	}
	
	@Override
	public void visit(CondRelops condRelops) {
		HashMap<Class, Integer> ops = new HashMap<>();
		ops.put(EqualOp.class, Code.eq);
		ops.put(NotEqualOp.class, Code.ne);
		ops.put(GreaterOp.class, Code.gt);
		ops.put(GreaterEqualOp.class, Code.ge);
		ops.put(LessOp.class, Code.lt);
		ops.put(LessEqualOp.class, Code.le);
		Code.putFalseJump(ops.get(condRelops.getRelops().getClass()), 0); //one condfact is false -> condterm is false -> jump to adr(after condterm)
		if (condRelops.getParent().getClass().equals(CondFactFor.class)) {
			patchesFor.peek().get(0).add(Code.pc-2);
		}
		else {
			patchesIf.peek().get(0).add(Code.pc-2);
		}
	}
	//=================================================================================
	// CondTerm ::=	
	@Override
	public void visit(NoCondAnd noCondAnd) {
	}
	
	@Override
	public void visit(CondAnd condAnd) {
	}	
	//=================================================================================
	//Condition ::=	
	@Override
	public void visit(NoCondOr noCondOr) {
		Code.putJump(0); //all condfacts are true -> condterm is true -> condition is true -> jump to adr(if)
		patchesIf.peek().get(1).add(Code.pc - 2);
		for (Integer i : patchesIf.peek().get(0)) {
			Code.fixup(i);
		}
		patchesIf.peek().get(0).clear();
	}

	@Override
	public void visit(CondOr condOr) {
		Code.putJump(0); //all condfacts are true -> condterm is true -> condition is true -> jump to adr(if)
		patchesIf.peek().get(1).add(Code.pc - 2);
		for (Integer i : patchesIf.peek().get(0)) {
			Code.fixup(i);
		}
		patchesIf.peek().get(0).clear();
	}	
	//=================================================================================
	// DesignStatement ::=	
	public void visit(DesignAssignment designAssignment){
		Code.store(designAssignment.getDesign().obj);
	}
	
	@Override
	public void visit(DesignInc designInc) {
		Code.loadConst(1);
		Code.put(Code.add);
		Code.store(designInc.getDesign().obj);
	}
	
	@Override
	public void visit(DesignDec designDec) {
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.store(designDec.getDesign().obj);
	}
	
	@Override
	public void visit(DesignMethCall designMethCall) {
		Obj methObj = designMethCall.getDesign().obj;
		int offset = methObj.getAdr() - Code.pc;
		Code.put(Code.call);
		Code.put2(offset);
		if(designMethCall.getDesign().obj.getType() != Tab.noType){ // This ret value isn't needed anywhere, cleaning stack
			Code.put(Code.pop);
		}
	}
	
	//=================================================================================
	// Designs ::=

	@Override
	public void visit(DesignsListFirstDesign designsListFirstDesign) {
		arrayAssignDests.add(designsListFirstDesign.obj);
	}
	
	@Override
	public void visit(DesignsListDesign designsListDesign) {
		arrayAssignDests.add(designsListDesign.obj);
	}
	
	@Override
	public void visit(DesignMultiAssignment designMultiAssignment) {
		Obj designArrDst = designMultiAssignment.getDesign().obj;
		Obj designArrSrc = designMultiAssignment.getDesign1().obj;
		int errorAdr, jumpAdr, loopArraysAssign;
		int i = 0;
		boolean isChar = (designArrSrc.getType().getElemType().getKind() == Struct.Char);
		
		
		Code.putJump(0);
		jumpAdr = Code.pc-2;
		String errorMsg = "Bad arr assign!"; // Comment if too big for buffer
		errorAdr = Code.pc;
		for (char c : errorMsg.toCharArray()) {
			Code.loadConst(c);
			Code.loadConst(1);
			Code.put(Code.bprint);
		}
		Code.put(Code.trap);
		Code.put(2);
		
		Code.fixup(jumpAdr);
		Code.loadConst(0);
		for (Obj dest : arrayAssignDests) {
			Code.put(Code.dup); //one for check, other for next loop inc and check,...
			loadArr(designArrSrc);
			Code.put(Code.arraylength);
			Code.putFalseJump(Code.ne, errorAdr);
			loadArr(designArrSrc);
			Code.loadConst(i);
			if (isChar) Code.put(Code.baload);
	        else Code.put(Code.aload);
			Code.store(dest);
			Code.loadConst(1);
			Code.put(Code.add);
			++i;
		}
		loadArr(designArrSrc);
		Code.put(Code.arraylength);
		Code.putFalseJump(Code.ne, errorAdr); //nothing left for arrDst
		
		Code.loadConst(0);
		loopArraysAssign = Code.pc;
		loadArr(designArrDst);
		Code.put(Code.dup2);
		Code.put(Code.pop); //only need the dst counter
		Code.put(Code.dup); //for calculating the src index
		Code.loadConst(i);
		Code.put(Code.add);
		loadArr(designArrSrc);
		Code.put(Code.dup2);
		Code.put(Code.pop); //only need the src index
		if (isChar) Code.put(Code.baload);
        else Code.put(Code.aload);
		if (isChar) Code.put(Code.bastore);
        else Code.put(Code.astore);
		Code.loadConst(1);
		Code.put(Code.add); //inc the dst counter 
		Code.put(Code.dup);
		loadArr(designArrDst);
		Code.put(Code.arraylength);
		Code.putFalseJump(Code.ge, loopArraysAssign);
		Code.put(Code.pop);
	}
	
	void loadArr (Obj o) {
		if (o.getLevel()==0) { // global variable 
			Code.put(Code.getstatic); Code.put2(o.getAdr()); 
	  	  	return; 
		}
		// local variable
		if (0 <= o.getAdr() && o.getAdr() <= 3) 
			Code.put(Code.load_n + o.getAdr());
		else { 
			Code.put(Code.load); Code.put(o.getAdr()); 
		} 
	}
	
}

package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;

public class SemanticAnalyzer extends VisitorAdaptor {

	public boolean errorDetected = false;
	private boolean mainFound = false;
	private static final String[] objKindNames = { "Con", "Var", "Type", "Meth", "Fld", "Elem", "Prog" };
	private static final String[] structKindNames = { "None", "Int", "Char", "Array", "Class", "Bool" };
	private Obj currType = null;
	private Obj currClass = null;
	private Obj currMethod = null;
	private String currNamespace = "";
	private boolean returnFound = true;
	private int numLoops = 0;
	private List<Struct> currParameters = new ArrayList<>();
	
	public static Struct boolType = new Struct(Struct.Bool);
	
	Logger log = Logger.getLogger(getClass());
	
	{
		Tab.currentScope.addToLocals(new Obj(Obj.Type, "bool", boolType));
	}

	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" (line ").append(line).append(")");
		log.error(msg.toString());
	}

	public void report_info(String message, Obj symbol, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message); 
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" (line ").append(line).append(")");
		String formattedSymbolInfo = String.format("[%s, %s, %s, %d, %d]",
		        symbol.getName(), objKindNames[symbol.getKind()],
		        structKindNames[symbol.getType().getKind()], symbol.getAdr(), symbol.getLevel());
		msg.append(formattedSymbolInfo);
		log.info(msg.toString());
	}
	
	
	//=================================================================================
	// Helper functions
	private void addParam(SyntaxNode paramNode, String paramName, Struct type) {
		if (currMethod == null) {
			// Error happened earlier.
			return;
		}
		Obj paramNameObj = Tab.find(paramName);
		if (paramNameObj.getKind() == Obj.Var && paramNameObj.getLevel() == 1) {
			report_error("Multiple parameters named " + paramName + "!", null);
			return;
		}
		Obj paramObj = Tab.insert(Obj.Var, paramName, type);
		report_info("Defined parameter in method " + currMethod.getName(), paramObj, paramNode);
		currMethod.setLevel(currMethod.getLevel() + 1);
		paramObj.setFpPos(currMethod.getLevel());
	}
	
	private boolean areParametersCompatible(Obj method) {
		if (method.getKind() != Obj.Meth || method.getLevel() != currParameters.size()) {
			return false;
		}
		ArrayList<Obj> formParams = new ArrayList<Obj>(method.getLocalSymbols());
		for (int i = 0; i < formParams.size(); ++i) {
			Obj formParam = formParams.get(i);
			int pos = formParam.getFpPos();
			if (pos == 0) { // a local variable, not formal parameter
				continue;
			}
			if (!(currParameters.get(pos - 1)).assignableTo(formParam.getType())) {
				return false;
			}
		}
		return true;
	}
	//=================================================================================
	// ProgName ::=
	@Override
    public void visit(ProgName progName){
    	progName.obj = Tab.insert(Obj.Prog, progName.getProgName(), Tab.noType);
    	if (progName.obj.getKind() != Obj.Prog) {
			report_error("Program cannot have the same name as a keyword!", progName);
			return;
		}
		report_info("Defined program type", progName.obj, progName);
    	Tab.openScope();
    }
	//=================================================================================
	// Program ::=
	@Override
    public void visit(Program program){
		program.obj = program.getProgName().obj;
    	Code.dataSize = Tab.currentScope.getnVars();
    	Tab.chainLocalSymbols(program.obj);
    	Tab.closeScope();
    	if (!mainFound) {
			report_error("Main method not found in the program!", null);
		}
    }
	//=================================================================================
	// NamespaceName ::=
	@Override
    public void visit(NamespaceName namespaceName){
		if (Tab.find(namespaceName.getNamespaceName()) != Tab.noObj) {
			report_error("Namespace " + namespaceName.getNamespaceName() + " already defined!", namespaceName);
			return;
    	}
		namespaceName.obj = Tab.insert(Obj.Prog, namespaceName.getNamespaceName(), Tab.nullType);
    	if (namespaceName.obj.getKind() != Obj.Prog) {
			report_error("Namespace cannot have the same name as a keyword!", namespaceName);
			namespaceName.obj = null;
			return;
		}
		report_info("Defined namespace type", namespaceName.obj, namespaceName);
		currNamespace = namespaceName.getNamespaceName() + "::";
    }
	//=================================================================================
	// Namespaces ::=
	@Override
    public void visit(ANamespace namespace){
		currNamespace = "";
		if (namespace.getNamespaceName().obj == null) {
			// Error happened earlier.
			return;
		}
    }
	//=================================================================================
	// Type ::=
	@Override
	public void visit(TypeSimple type){
    	Obj typeObj = Tab.find(currNamespace + type.getTypeName());
    	currType = null;
		type.struct = Tab.noType;
		if (typeObj == Tab.noObj){
			typeObj = Tab.find(type.getTypeName());
		}
    	if (typeObj == Tab.noObj){
    		report_error("No type " + type.getTypeName() + " declared in the symbol table!", type);
    		return;
    	} 
    	if(Obj.Type != typeObj.getKind()){
			report_error("Name " + type.getTypeName() + " is not of type kind!", type);
			return;
		} 
    	currType = typeObj;
		type.struct = typeObj.getType();
    }
	
	@Override
	public void visit(TypeSpecific type){
		String namespace = type.getNamespaceName();
		Obj namespaceObj = Tab.find(namespace);
		currType = null;
		type.struct = Tab.noType;
		if (namespaceObj == Tab.noObj) {
    		report_error("No namespace " + namespace + " declared in the symbol table!", type);
    		return;
    	}
		if(Obj.Prog != namespaceObj.getKind() || Tab.nullType != namespaceObj.getType()){	
			report_error("Name " + type.getTypeName() + " is not of namespace kind!", type);
			return;
		}
		String typeName = namespace + type.getTypeName();
		Obj typeObj = Tab.find(typeName);
    	if(typeObj == Tab.noObj){
    		report_error("No type " + typeName + " declared in the symbol table!", type);
    		return;
    	}
    	if (Obj.Type != typeObj.getKind()){
			report_error("Name " + typeName + " is not of type kind!", type);
			return;
		}
    	currType = typeObj;
		type.struct = typeObj.getType();
	}
	//=================================================================================
	// ConstDeclSingle ::=
	@Override
	public void visit(SingleConstDecl constDecl) {
		if (currType == null) {
			// Error happened earlier.
			return;
		}
		if (!constDecl.getConstValue().obj.getType().equals(currType.getType())) {
			report_error("Incompatible types in declaration of " + currNamespace + constDecl.getName() + "!", constDecl);
			return;
		}
		if (Tab.find(currNamespace + constDecl.getName()) != Tab.noObj) {
			report_error("Constant " + currNamespace + constDecl.getName() + " already defined!", constDecl);
			return;
		}
		Obj constObj = Tab.insert(Obj.Con, currNamespace + constDecl.getName(), constDecl.getConstValue().obj.getType());
		constObj.setAdr(constDecl.getConstValue().obj.getAdr());
		report_info("Constant declaration", constObj, constDecl);
	}
	//=================================================================================
	// VarArr ::=
	@Override
	public void visit(ArrVar arrVar) {
		if (currType == null) {
			// Error happened earlier.
			return;
		}
		arrVar.struct = new Struct(Struct.Array, currType.getType());
	}

	@Override
	public void visit(NotArrVar notArrVar) {
		if (currType == null) {
			// Error happened earlier.
			return;
		}
		notArrVar.struct = currType.getType();
	}
	//=================================================================================
	// VarDeclSingle ::=
	@Override
	public void visit(SingleVarDecl varDecl) {
		Struct varType = varDecl.getVarArr().struct; // the info if it is an array and it's type set
		Obj varTypeObj = Tab.find(currNamespace + varDecl.getName());
		if (varTypeObj != Tab.noObj) {
			if (currMethod == null) {
				report_error("Variable " + currNamespace + varDecl.getName() + " already defined!", varDecl);
				return;
			} else if (varTypeObj.getLevel() != 0) {
				report_error("Local variable " + currNamespace + varDecl.getName() + " already defined!", varDecl);
				return;
			}
		}
		if (varType == null) {
			// Error happened earlier.
			return;
		}
		int objKind = (currClass == null || currMethod != null)? Obj.Var : Obj.Fld;
		Obj varObj = Tab.insert(objKind, currNamespace + varDecl.getName(), varType);
		report_info("Variable declaration", varObj, varDecl);
	}
	//=================================================================================
	// ConstValue ::=
	@Override
	public void visit(NumConst numConst) {
		numConst.obj = new Obj(Obj.Con, "const", Tab.intType, numConst.getNumConst(), 0);
	}

	@Override
	public void visit(CharConst charConst) {
		charConst.obj = new Obj(Obj.Con, "const", Tab.charType, (int) charConst.getCharConst(), 0);
	}

	@Override
	public void visit(BoolConst boolConst) {
		boolConst.obj = new Obj(Obj.Con, "const", boolType, boolConst.getBoolConst() ? 1 : 0, 0);
	}
	//=================================================================================
	// ReturnType ::=
	@Override
	public void visit(ReturnTypeVoid returnTypeVoid) {
		currType = null;
	}
	//=================================================================================
	// MethName ::=
	@Override
	public void visit(MethName methName) {
		Obj methNameObj = Tab.find(currNamespace + methName.getMethName());
		if (methNameObj != Tab.noObj && methNameObj.getKind() != Obj.Meth && methNameObj.getLevel() > 0) {
			report_error("Method name " + currNamespace + methName.getMethName() + " already used for another symbol, name conflict!", methName);
			return;
		}
		currMethod = Tab.insert(Obj.Meth, currNamespace + methName.getMethName(),
				(currType == null) ? Tab.noType : currType.getType());
		if (currType != null)
			returnFound = false;
		else
			returnFound = true;
		currMethod.setLevel(0);
		report_info("Method declaration", currMethod, methName);
		currType = null;
		Tab.openScope();
		if (currClass != null) {
			addParam(methName, currNamespace+"this", currClass.getType());
		} 
		else if (methName.getMethName().equalsIgnoreCase("main")) {
			if (currMethod.getType() != Tab.noType) {
				report_error("The main() method must be declared void!", methName);
			} else {
				mainFound = true;
			}
		}
		methName.obj = currMethod;
	}
	//=================================================================================
	// MethodDecl ::=
	@Override
	public void visit(MethDecl methDecl) {
		if (currMethod == null) {
			// Error happened earlier.
			return;
		}
		if (!returnFound) {
			report_error("No return found in non void method!", methDecl);
		}
		Tab.chainLocalSymbols(currMethod);
		Tab.closeScope();
		methDecl.obj = currMethod;
		currMethod = null;
	}
	//=================================================================================
	// FormParsList ::=
	@Override
	public void visit(FirstFormParams firstFormParams) {
		addParam(firstFormParams, currNamespace+firstFormParams.getName(), firstFormParams.getVarArr().struct);
		currType = null;
	}
	
	@Override
	public void visit(ListFormParams listFormParams) {
		addParam(listFormParams, currNamespace+listFormParams.getName(), listFormParams.getVarArr().struct);
		currType = null;
	}
	//=================================================================================
	// FormPars ::=
	@Override
	public void visit(NoFormParams noFormParams) {
		currType = null;
	}
	//=================================================================================
	// Statement ::= basic ones
	@Override
	public void visit(StmntRead stmntRead) {
		Obj designObj = stmntRead.getDesign().obj;
		if (designObj == null) {
			// Error happened earlier.
			return;
		}
		if (designObj.getKind() != Obj.Var && designObj.getKind() != Obj.Elem && designObj.getKind() != Obj.Fld) {
			report_error("Designator " + designObj.getName() + " can't be read!", stmntRead);
			return;
		}
		if (!designObj.getType().equals(Tab.intType) && !designObj.getType().equals(Tab.charType) && !designObj.getType().equals(boolType)) {
			report_error("Can't read, designator type can only be integer, character or boolean!", stmntRead);
		}
	}
	
	@Override
	public void visit(StmntPrint stmntPrint) {
		Struct exprStruct = stmntPrint.getExpr().struct;
		if (exprStruct == null) {
			report_error("No expression to print!", stmntPrint);
			return;
		}
		if (!exprStruct.equals(Tab.intType) && !exprStruct.equals(Tab.charType) && !exprStruct.equals(boolType)) {
			report_error("Can't print, type can only be integer, character or boolean!", stmntPrint);
		}
	}
	
	@Override
	public void visit(StmntRetVoid stmntRetVoid) {
		if (currMethod == null) {
			report_error("No return allowed outside method body!", stmntRetVoid);
			return;
		}
		if (currMethod.getType() != Tab.noType) {
			report_error("The method " + currMethod.getName() + " isn't declared to return void!", stmntRetVoid);
		}
	}
	
	@Override
	public void visit(StmntRetExpr stmntRetExpr) {
		if (currMethod == null) {
			report_error("No return allowed outside method body!", stmntRetExpr);
			return;
		}
		Struct exprStruct = stmntRetExpr.getExpr().struct;
		if (!currMethod.getType().equals(exprStruct)) {
			report_error("The method " + currMethod.getName() + " isn't declared to return this type!", stmntRetExpr);
			return;
		}
		returnFound = true;
	}
	//=================================================================================
	// Statement ::= for parts
	@Override
	public void visit(BeforeFor beforeFor) {
		++numLoops;
	}
	@Override
	public void visit(StmntContinue beforeFor) {
		if (numLoops == 0) {
			report_error("No continue allowed outside for loop!", beforeFor);
			return;
		}
	}
	@Override
	public void visit(StmntBreak beforeBreak) {
		if (numLoops == 0) {
			report_error("No break allowed outside for loop!", beforeBreak);
			return;
		}
	}
	@Override
	public void visit(StmntForCond stmntForCond) {
		--numLoops;
	}
	@Override
	public void visit(CondFactFor condFactFor) {
		if (!condFactFor.getCondFact().struct.equals(boolType)) {
			report_error("Condition in for loop isn't boolean!", condFactFor);
			return;
		}
	}
	//=================================================================================
	// Statement ::= if parts
	@Override
	public void visit(StmntIfElse stmntIfElse) {
		if (!stmntIfElse.getCondition().struct.equals(boolType)) {
			report_error("Condition in if condition isn't boolean!", stmntIfElse);
			return;
		}
	}
	//=================================================================================
	// Design (lvl B) ::=
	@Override
	public void visit(DesignIdentNamespace designIdentNamespace) {
		String designNamespace = designIdentNamespace.getNamespaceName();
		Obj designNamespaceObj = Tab.find(designNamespace);
		if (designNamespaceObj == Tab.noObj || designNamespaceObj.getKind() != Obj.Prog || designNamespaceObj.getType() != Tab.nullType) {
			report_error("Namespace " + designNamespace + " doesn't exist!", designIdentNamespace);
			designIdentNamespace.obj = null;
			return;
		}
		String designIdentFull = designNamespace + "::" + designIdentNamespace.getVarName();
		Obj designObj = Tab.find(designIdentFull);
		designIdentNamespace.obj = designObj;
		if (designObj == Tab.noObj ||
				!(designObj.getKind() == Obj.Con || designObj.getKind() == Obj.Var || designObj.getKind() == Obj.Type || designObj.getKind() == Obj.Meth)) {
			report_error("Symbol " + designIdentFull + " doesn't exist or can't be addressed in this form!", designIdentNamespace);
			designIdentNamespace.obj = null;
			return;
		}
	}
	
	@Override
	public void visit(DesignIdent designIdent) {
		String designIdentFull = currNamespace + designIdent.getVarName();
		Obj designObj = Tab.find(designIdentFull);
		designIdent.obj = designObj;
		if (designObj == Tab.noObj && !currNamespace.equals("")) {
			designIdentFull = designIdent.getVarName();
			designObj = Tab.find(designIdentFull);
			designIdent.obj = designObj;
		}
		if (designObj == Tab.noObj || (!(designObj.getKind() == Obj.Con || designObj.getKind() == Obj.Var || designObj.getKind() == Obj.Type || designObj.getKind() == Obj.Meth))) {
			report_error("Symbol " + designIdentFull + " doesn't exist or can't be addressed in this form!", designIdent);
			designIdent.obj = null;
			return;
		}
	}
	
	@Override
	public void visit(DesignArrayAccess designArrayAccess) {
		Obj designToAccesObj = designArrayAccess.getDesign().obj;
		designArrayAccess.obj = null;
		if (designToAccesObj == null) {
			// Error happened earlier.
			return;
		}
		if (designToAccesObj.getType().getKind() != Struct.Array) {
			report_error("Symbol " + designToAccesObj.getName() + " isn't an array!", designArrayAccess);
			return;
		}
		Struct indexToAccesStruct = designArrayAccess.getExpr().struct;
		if (indexToAccesStruct == null) {
			// Error happened earlier.
			return;
		}
		if (!indexToAccesStruct.equals(Tab.intType)) {
			report_error("Index isn't an integer!", designArrayAccess);
			return;
		}
		designArrayAccess.obj = new Obj(Obj.Elem, "arrayElem", designToAccesObj.getType().getElemType());
	}
	
	//=================================================================================
	// Factor (lvl B) ::=
	@Override
	public void visit(FactorConst factorConst) {
		factorConst.struct = factorConst.getConstValue().obj.getType();
	}
	
	@Override
	public void visit(FactorDesign factorDesign) {
		factorDesign.struct = null;
		if (factorDesign.getDesign().obj == null) {
			// Error happened earlier.
			return;
		}
		factorDesign.struct = factorDesign.getDesign().obj.getType();
	}
	
	@Override
	public void visit(FactorExpr factorExpr) {
		factorExpr.struct = null;
		if (factorExpr.getExpr().struct == null) {
			// Error happened earlier.
			return;
		}
		factorExpr.struct = factorExpr.getExpr().struct;
	}
	
	@Override
	public void visit(FactorNewArrRef factorNewArrRef) {
		if (currType == null) {
			factorNewArrRef.struct = null;
			return;
		}
		if (!factorNewArrRef.getExpr().struct.equals(Tab.intType)) {
			report_error("New array size isn't an integer!", factorNewArrRef);
			factorNewArrRef.struct = null;
			return;
		}
		factorNewArrRef.struct = new Struct(Struct.Array, currType.getType());
		report_info("New array instantiated", currType, factorNewArrRef);
		currType = null;
	}
	
	@Override
	public void visit(FactorDesignFCall factorDesignFCall) {
		Obj methodObj = factorDesignFCall.getDesign().obj;
		factorDesignFCall.struct = null;
		if (methodObj == null) {
			// Error happened earlier.
			return;
		}
		if (methodObj.getKind() != Obj.Meth) {
			report_error(methodObj.getName() + "cannot be called, not a method", factorDesignFCall);
			return;
		}
		if (methodObj.getType() == Tab.noType) {
			report_error(methodObj.getName() + " returns void, cannot be assigned", factorDesignFCall);
			return;
		}
		//currParameters already set in ActPars 
		if (!areParametersCompatible(methodObj)) {
			report_error("Incompatible parameter types in method call!", factorDesignFCall);
			return;
		}
		factorDesignFCall.struct = methodObj.getType();
		currParameters.clear();
	}
	//=================================================================================
	// Term ::=
	@Override
	public void visit(NoMulopsTerm noMulopsTerm) {
		noMulopsTerm.struct = noMulopsTerm.getFactor().struct;
	}

	@Override
	public void visit(MulopsTerm mulopsTerm) {
		if (!mulopsTerm.getTerm().struct.equals(Tab.intType) || !mulopsTerm.getFactor().struct.equals(Tab.intType)) {
			report_error("Terms to multiply/divide aren't both integers!", mulopsTerm);
			mulopsTerm.struct = null;
			return;
		}
		mulopsTerm.struct = mulopsTerm.getFactor().struct;
	}
	//=================================================================================
	// Expr ::=
	@Override
	public void visit(NoAddopsExpr noAddopsExpr) {
		noAddopsExpr.struct = noAddopsExpr.getTerm().struct;
	}

	@Override
	public void visit(AddopsExpr addopsExpr) {
		if (!addopsExpr.getExpr().struct.equals(Tab.intType) || !addopsExpr.getTerm().struct.equals(Tab.intType)) {
			report_error("Terms to add/substract aren't both integers!", addopsExpr);
			addopsExpr.struct = null;
			return;
		}
		addopsExpr.struct = addopsExpr.getTerm().struct;
	}

	@Override
	public void visit(NoAddopsExprNeg noAddopsExprNeg) {
		if (!noAddopsExprNeg.getTerm().struct.equals(Tab.intType)) {
			report_error("Term to be negated isn't of type integer!", noAddopsExprNeg);
			noAddopsExprNeg.struct = null;
			return;
		}
		noAddopsExprNeg.struct = noAddopsExprNeg.getTerm().struct;
	}
	//=================================================================================
	// CondFact ::=	
	@Override
	public void visit(NoCondRelops noCondRelops) {
		noCondRelops.struct = noCondRelops.getExpr().struct;
	}
	
	@Override
	public void visit(CondRelops condRelops) {
		Struct expr1Obj = condRelops.getExpr().struct;
		Struct expr2Obj = condRelops.getExpr1().struct;
		if (!(expr1Obj.compatibleWith(expr2Obj))) {
			report_error("Expressions aren't compatible to compare!", condRelops);
			condRelops.struct = null;
			return;
		}
		if (expr1Obj.isRefType() || expr2Obj.isRefType()) {
			if (!((condRelops.getRelops() instanceof EqualOp) || (condRelops.getRelops() instanceof NotEqualOp))) {
				report_error("Expressions of type array/class can't be compared this way!", condRelops);
				condRelops.struct = null;
				return;
			}
		}
		condRelops.struct = boolType;
	}
	//=================================================================================
	// CondTerm ::=	
	@Override
	public void visit(NoCondAnd noCondAnd) {
		noCondAnd.struct = noCondAnd.getCondFact().struct;
	}
	
	@Override
	public void visit(CondAnd condAnd) {
		if (!condAnd.getCondTerm().struct.equals(boolType) || !condAnd.getCondFact().struct.equals(boolType)) {
			report_error("Condition factors aren't both boolean!", condAnd);
			condAnd.struct = null;
			return;
		}
		condAnd.struct = condAnd.getCondTerm().struct;
	}	
	//=================================================================================
	// Condition ::=	
	@Override
	public void visit(NoCondOr noCondOr) {
		noCondOr.struct = noCondOr.getCondTerm().struct;
	}

	@Override
	public void visit(CondOr condOr) {
		if (!condOr.getCondition().struct.equals(boolType) || !condOr.getCondTerm().struct.equals(boolType)) {
			report_error("Condition terms aren't both boolean!", condOr);
			condOr.struct = null;
			return;
		}
		condOr.struct = condOr.getCondition().struct;
	}	
	//=================================================================================
	// DesignStatement ::=	
	@Override
	public void visit(DesignAssignment designAssignment) {
		Obj designObj = designAssignment.getDesign().obj;
		Struct exprStruct = designAssignment.getExpr().struct;
		if (designObj == null || exprStruct == null) {
			// Error happened earlier.
			return;
		}
		if (designObj.getKind() != Obj.Var && designObj.getKind() != Obj.Elem && designObj.getKind() != Obj.Fld) {
			report_error("Designator " + designObj.getName() + " can't be assigned to!", designAssignment);
			return;
		}
		if (!exprStruct.assignableTo(designObj.getType())) {
			report_error("Expression type incompatible for assigning to " + designObj.getName() + "!", designAssignment);
			return;
		}
	}
	
	@Override
	public void visit(DesignInc designInc) {
		Obj designObj = designInc.getDesign().obj;
		if (designObj.getKind() != Obj.Var && designObj.getKind() != Obj.Elem && designObj.getKind() != Obj.Fld) {
			report_error("Designator " + designObj.getName() + " can't be incremented due to kind!", designInc);
			return;
		}
		if (!designObj.getType().equals(Tab.intType)) {
			report_error("Designator to increment " + designObj.getName() + "isn't an integer!", designInc);
			return;
		}
	}
	
	@Override
	public void visit(DesignDec designDec) {
		Obj designObj = designDec.getDesign().obj;
		if (designObj.getKind() != Obj.Var && designObj.getKind() != Obj.Elem && designObj.getKind() != Obj.Fld) {
			report_error("Designator " + designObj.getName() + " can't be decremented due to kind!", designDec);
			return;
		}
		if (!designObj.getType().equals(Tab.intType)) {
			report_error("Designator to decrement " + designObj.getName() + "isn't an integer!", designDec);
			return;
		}
	}
	
	@Override
	public void visit(DesignMethCall designMethCall) {
		Obj method = designMethCall.getDesign().obj;
		if (method.getKind() != Obj.Meth) {
			report_error(method.getName() + "cannot be called, not a method", designMethCall);
			return;
		}
		//currParameters already set in ActPars 
		if (!areParametersCompatible(method)) {
			report_error("Incompatible parameter types in method call!", designMethCall);
			return;
		}
		currParameters.clear();
	}
	
	@Override
	public void visit(DesignMultiAssignment designMultiAssignment) {
		Obj designsDst = designMultiAssignment.getDesigns().obj;
		Obj designArrDst = designMultiAssignment.getDesign().obj;
		Obj designArrSrc = designMultiAssignment.getDesign1().obj;
		if (designArrSrc.getType().getKind() != Struct.Array) {
			report_error("Value on the right side isn't of array type!", designMultiAssignment);
			return;
		}
		if (designArrDst.getType().getKind() != Struct.Array) {
			report_error("Value of * on the left side isn't of array type!", designMultiAssignment);
			return;
		}
		if (designsDst == null) {
			report_error("Values on the left side aren't of the right kind or have different types!", designMultiAssignment);
			return;
		}
		if (!designArrSrc.getType().assignableTo(designArrDst.getType()) && !designArrSrc.getType().getElemType().assignableTo(designsDst.getType())) {
			report_error("Designators have to be of comatible (assignable) types!", designMultiAssignment);
			return;
		}
	}
	//=================================================================================
	// Designs ::=
	@Override
	public void visit(DesignsListNoDesign designsListNoDesign) {
		designsListNoDesign.obj = null;
		Obj designsBeforeObj = designsListNoDesign.getDesigns().obj;
		if (designsBeforeObj == null) {
			// Error happened earlier.
			return;
		}
		designsListNoDesign.obj = designsBeforeObj;
	}
	
	@Override
	public void visit(DesignsListFirstDesign designsListFirstDesign) {
		designsListFirstDesign.obj = null;
		Obj designObj = designsListFirstDesign.getDesign().obj;
		if (designObj == null) {
			// Error happened earlier.
			return;
		}
		if (designObj.getKind() != Obj.Var && designObj.getKind() != Obj.Elem && designObj.getKind() != Obj.Fld) {
			report_error("First designator isn't of variable, elem nor field kind!", designsListFirstDesign);
			return;
		}
		designsListFirstDesign.obj = designObj;
	}
	
	@Override
	public void visit(DesignsListDesign designsListDesign) {
		designsListDesign.obj = null;
		Obj designsBeforeObj = designsListDesign.getDesigns().obj;
		Obj designObj = designsListDesign.getDesign().obj;
		if (designsBeforeObj == null || designObj == null) {
			// Error happened earlier.
			return;
		}
		if (designObj.getKind() != Obj.Var && designObj.getKind() != Obj.Elem && designObj.getKind() != Obj.Fld) {
			report_error("Designator isn't of variable, elem nor field kind!", designsListDesign);
			return;
		}
		if (!designsBeforeObj.getType().equals(Tab.noObj.getType()) && !designsBeforeObj.getType().equals(designObj.getType())) {
			report_error("Designators have to be of the same type!", designsListDesign);
			return;
		}
		designsListDesign.obj = designObj;
	}
	@Override
	public void visit(NoDesignsList noDesignsList) {
		noDesignsList.obj = Tab.noObj;
	}
	//=================================================================================
	// ActParsList ::=	
	@Override
	public void visit(FirstActPars firstActPars) {
		Struct exprStruct = firstActPars.getExpr().struct;
		if (exprStruct == null) {
			// Error happened earlier.
			return;
		}
		currParameters.add(exprStruct);
	}
	
	@Override
	public void visit(ListActPars listActPars) {
		Struct exprStruct = listActPars.getExpr().struct;
		if (exprStruct == null || currParameters.isEmpty()) {
			// Error happened earlier.
			return;
		}
		currParameters.add(exprStruct);
	}
	
}

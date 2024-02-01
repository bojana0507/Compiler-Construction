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
	
	
	// HELPER FUNCTIONS
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
	
	@Override
    public void visit(NamespaceName namespaceName){
		if (Tab.find(namespaceName.getNamespaceName()) != Tab.noObj) {
			report_error("Namespace " + namespaceName.getNamespaceName() + " already defined!", namespaceName);
			return;
    	}
		namespaceName.obj = Tab.insert(Obj.Prog, namespaceName.getNamespaceName(), Tab.noType);
    	if (namespaceName.obj.getKind() != Obj.Prog) {
			report_error("Namespace cannot have the same name as a keyword!", namespaceName);
			namespaceName.obj = null;
			return;
		}
		report_info("Defined namespace type", namespaceName.obj, namespaceName);
		currNamespace = namespaceName.getNamespaceName() + "::";
    }
	
	@Override
    public void visit(ANamespace namespace){
		currNamespace = "";
		if (namespace.getNamespaceName().obj == null) {
			// Error happened earlier.
			return;
		}
    }
	
	@Override
	public void visit(TypeSimple type){
    	Obj typeObj = Tab.find(type.getTypeName());
    	currType = null;
		type.struct = Tab.noType;
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
		String typeName = currNamespace + type.getTypeName();
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
	
	@Override
	public void visit(SingleVarDecl varDecl) {
		Struct varType = varDecl.getVarArr().struct; // the info if it is an array and it's type set
		Obj varTypeObj = Tab.find(currNamespace + varDecl.getName());
		if (varTypeObj != Tab.noObj) {
			if (currMethod == null) {
				report_error("Variable " + currNamespace + varDecl.getName() + " already defined!", varDecl);
				return;
			} else if (varTypeObj.getLevel() != 0) {
				report_error("Local variable " + varDecl.getName() + " already defined!", varDecl);
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
	
	@Override
	public void visit(ReturnTypeVoid returnTypeVoid) {
		currType = null;
	}
	
	@Override
	public void visit(MethName methName) {
		Obj methNameObj = Tab.find(currNamespace + methName.getMethName());
		if (methNameObj != Tab.noObj && methNameObj.getKind() != Obj.Meth && methNameObj.getLevel() > 0) {
			report_error("Method name " + currNamespace + methName.getMethName() + " already used for another symbol, name conflict!", methName);
			return;
		}
		currMethod = Tab.insert(Obj.Meth, currNamespace + methName.getMethName(),
				(currType == null) ? Tab.noType : currType.getType());
		currMethod.setLevel(0);
		report_info("Method declaration", currMethod, methName);
		currType = null;
		Tab.openScope();
		if (currClass != null) {
//			addParam("this", currClass.getType());
		} else if (methName.getMethName().equals("main")) {
			if (currMethod.getType() != Tab.noType) {
				report_error("The main() method must be declared void!", methName);
			} else {
				mainFound = true;
			}
		}
		methName.obj = currMethod;
	}

	@Override
	public void visit(MethDecl methDecl) {
		if (currMethod == null) {
			// Error happened earlier.
			return;
		}
		Tab.chainLocalSymbols(currMethod);
		Tab.closeScope();
		methDecl.obj = currMethod;
		currMethod = null;
	}
	
	@Override
	public void visit(FirstFormParams firstFormParams) {
		addParam(firstFormParams, firstFormParams.getName(), firstFormParams.getVarArr().struct);
		currType = null;
	}
	
	@Override
	public void visit(ListFormParams listFormParams) {
		addParam(listFormParams, listFormParams.getName(), listFormParams.getVarArr().struct);
		currType = null;
	}
	
	@Override
	public void visit(NoFormParams noFormParams) {
		currType = null;
	}
	
	@Override
	public void visit(StmntRetVoid stmntRetVoid) {
		if (currMethod.getType() != Tab.noType) {
			report_error("The method " + currMethod.getName() + " isn't declared to return void!", stmntRetVoid);
			currMethod = null;
		}
	}
	
	@Override
	public void visit(StmntRetExpr stmntRetExpr) {
		if (currMethod.getType() == Tab.noType) {
			report_error("The method " + currMethod.getName() + " is declared to return void!", stmntRetExpr);
			currMethod = null;
		}
	}
	
}

package rs.ac.bg.etf.pp1;

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

	
	@Override
    public void visit(ProgName progName){
    	progName.obj = Tab.insert(Obj.Prog, progName.getProgName(), Tab.noType);
    	if (progName.obj.getKind() != Obj.Prog) {
			report_error("Program cannot have the same name as a keyword", progName);
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
			report_error("Main method not found in the program.", null);
		}
    }
	
	@Override
    public void visit(NamespaceName namespaceName){
		if (Tab.find(namespaceName.getNamespaceName()) != Tab.noObj) {
			report_error("Namespace " + namespaceName.getNamespaceName() + " already defined", namespaceName);
			return;
    	}
		namespaceName.obj = Tab.insert(Obj.Prog, namespaceName.getNamespaceName(), Tab.noType);
    	if (namespaceName.obj.getKind() != Obj.Prog) {
			report_error("Namespace cannot have the same name as a keyword", namespaceName);
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
			report_error("Incompatible types in declaration of " + currNamespace + constDecl.getName(), constDecl);
			return;
		}
		if (Tab.find(currNamespace + constDecl.getName()) != Tab.noObj) {
			report_error("Constant " + currNamespace + constDecl.getName() + " already defined", constDecl);
			return;
		}
		Obj constObj = Tab.insert(Obj.Con, currNamespace + constDecl.getName(), constDecl.getConstValue().obj.getType());
		constObj.setAdr(constDecl.getConstValue().obj.getAdr());
		report_info("Constant declaration", constObj, constDecl);
	}
	
	@Override
	public void visit(SingleVarDecl varDecl) {
		Struct varType = varDecl.getVarArr().struct; // the info if it is an array and it's type set
		if (Tab.find(currNamespace + varDecl.getName()) != Tab.noObj) {
			report_error("Variable " + currNamespace + varDecl.getName() + " already defined", varDecl);
			return;
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
	public void visit(ArrVar node) {
		if (currType == null) {
			// Error happened earlier.
			return;
		}
		node.struct = new Struct(Struct.Array, currType.getType());
	}

	@Override
	public void visit(NotArrVar node) {
		if (currType == null) {
			// Error happened earlier.
			return;
		}
		node.struct = currType.getType();
	}
    
}

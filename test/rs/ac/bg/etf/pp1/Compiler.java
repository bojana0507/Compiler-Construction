package rs.ac.bg.etf.pp1;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;

import org.apache.log4j.Logger;
import org.apache.log4j.xml.DOMConfigurator;

import java_cup.runtime.Symbol;
import rs.ac.bg.etf.pp1.ast.Program;
import rs.ac.bg.etf.pp1.ast.SyntaxNode;
import rs.ac.bg.etf.pp1.util.Log4JUtils;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.mj.runtime.Run;
import rs.etf.pp1.mj.runtime.disasm;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.*;

public class Compiler {

	static {
		DOMConfigurator.configure(Log4JUtils.instance().findLoggerConfigFile());//DOMConfigurator.configure("config/log4j.xml");
		Log4JUtils.instance().prepareLogFile(Logger.getRootLogger());
	}
	
	public static void main(String[] args) throws Exception {
		Logger log = Logger.getLogger(Compiler.class);
		if (args.length < 2) {
			log.error("Not enough arguments supplied! Usage: MJParser <source-file> <obj-file> ");
			System.exit(1);
		}
		
		File sourceCode = new File(args[0]);
		log.info("Compiling source file: " + sourceCode.getAbsolutePath());
		
		try (BufferedReader br = new BufferedReader(new FileReader(sourceCode))) {
			Yylex lexer = new Yylex(br);
			MJParser parser = new MJParser(lexer);
	        Symbol symbol = parser.parse();
	        if (parser.errorDetected) {
				log.error("SYNTAX ERROR DETECTED - process stopped.");
				System.exit(2);
			}
	        Program prog = (Program)(symbol.value);
	        log.debug(prog.toString(""));
			Tab.init(); // Universe scope
			
			SemanticAnalyzer semanticCheck = new SemanticAnalyzer();
			prog.traverseBottomUp(semanticCheck);
			
	        Tab.dump();
	        if (semanticCheck.errorDetected) {
				log.error("SEMANTIC ERROR DETECTED - process stopped");
				System.exit(3);
			}
        	File objFile = new File(args[1]);
        	log.info("Generating bytecode file: " + objFile.getAbsolutePath());
        	if (objFile.exists())
        		objFile.delete();
        	
        	// Code generation...
        	CodeGenerator codeGenerator = new CodeGenerator();
        	prog.traverseBottomUp(codeGenerator);
        	Code.write(new FileOutputStream(objFile));
        	if (args.length == 3) {
		        if (args[2].equals("--debug")) { 
					disasm.main(new String[] {args[1]});
				}
				if (args[2].equals("--run")) {
					Run.main(new String[] {args[1]});
				}
        	}
	        log.info("Compilation successful!");
		} catch (FileNotFoundException e) {
			log.error("Source file [" + sourceCode.getAbsolutePath() + "] missing!");
			System.exit(4);
		} catch (IOException e) {
			log.error("Unknown IO error.", e);
			System.exit(5);
		} catch (Exception e) {
			log.error("Unknown error.", e);
			System.exit(6);
		}
	}
}

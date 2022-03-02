package com.ibm.wala.examples.drivers;

import com.ibm.wala.cast.ir.ssa.AstIRFactory;
import com.ibm.wala.cast.js.ipa.callgraph.JSCallGraphUtil;
import com.ibm.wala.cast.js.translator.CAstRhinoTranslatorFactory;
import com.ibm.wala.cast.types.AstMethodReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.*;
import com.ibm.wala.util.WalaException;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import static com.ibm.wala.examples.drivers.FormatorAndRrcorder.dumpData;
import static com.ibm.wala.examples.drivers.FormatorAndRrcorder.getConcatData;
import static com.ibm.wala.examples.drivers.PathGenerator.getPathsFromIR;
import static com.ibm.wala.examples.drivers.core.TaintAnalyze.*;


public class JSCallGraphDriver {

    public static boolean debuggable = true;
    public static String res_dir = "";

    /**
     * Usage: JSCallGraphDriver js_files_dir entry.json_dir res_dir
     */
    public static void main(String[] args) throws IllegalArgumentException, WalaException {
        if (debuggable){
            // just for test single page.js
            String pathStr = "C:\\Users\\Lac\\Desktop\\test.js";
            res_dir = "C:\\Users\\Lac\\Desktop";
            String targetDataName = "url";
            analyzeSinglePage(pathStr, targetDataName);
        } else {
            // todo 跑多个文件
        }
    }


    public static void analyzeSinglePage(String pathStr, String targetDataName) throws ClassHierarchyException {
        if (targetDataName.equals("")) {
            System.out.println("No Target Data-field, impossible!");
            return;
        }
        JSCallGraphUtil.setTranslatorFactory(new CAstRhinoTranslatorFactory());
        IClassHierarchy cha = JSCallGraphUtil.makeHierarchyForScripts(pathStr);
        IRFactory<IMethod> factory = AstIRFactory.makeDefaultFactory();
        for (IClass klass : cha) {
            // ignore models of built-in JavaScript methods
            if (!klass.getName().toString().startsWith("Lprologue.js")) {
                // get the IMethod representing the code (the do method)
                IMethod m = klass.getMethod(AstMethodReference.fnSelector);
                // 锁定onLoad函数
                if (m != null && m.getSignature().contains(":onLoad.")) {
                    System.out.println("Begin analyze " + pathStr);
                    // init
                    IR ir = factory.makeIR(m, Everywhere.EVERYWHERE, new SSAOptions());
                    SSACFG cfg = ir.getControlFlowGraph();
                    SymbolTable symbolTable = ir.getSymbolTable();
                    List<InvokePath> paths = getPathsFromIR(ir, cfg);
                    // 分析每一条路径le
                    HashSet<Integer> allTaintMainVal = new HashSet<>(), allTaintCatVal = new HashSet<>();
                    List<InvokePath> hasTaintPaths = new LinkedList<>(), noTaintPaths = new LinkedList<>();
                    // 拼接变量的相关fieldName，可以直接用的
                    HashSet<String> concatFieldName = new HashSet<>();
                    // 参数的哪些属性是传入sink的
                    HashSet<String> valuableFieldNames = new HashSet<>();
                    for (InvokePath invokePath : paths) {
                        if (hasTaintFlow(invokePath, symbolTable, targetDataName, allTaintMainVal, allTaintCatVal, valuableFieldNames, concatFieldName)) {
                            hasTaintPaths.add(invokePath);
                        } else {
                            noTaintPaths.add(invokePath);
                        }
                    }
                    // 选一个目标field名称
                    String valFieldName = null;
                    if (valuableFieldNames.size() == 1){
                        valFieldName = (String) valuableFieldNames.toArray()[0];
                    } else {
                        String[] proityNames = new String[]{
                                "url", "h5url", "h5"
                        };
                        for (String t : proityNames){
                            if (valuableFieldNames.contains(t)){
                                valFieldName = t;
                                break;
                            }
                        }
                        if (valFieldName == null){
                            valFieldName = (String) valuableFieldNames.toArray()[0];
                        }
                    }
                    // 规则
                    HashSet<String> concatData = new HashSet<>();
                    ResultType type;
                    if (noTaintPaths.isEmpty()) {
                        System.out.println("No-Check for input url");
                        concatData = getConcatData(symbolTable, allTaintCatVal, concatFieldName);
                        type = ResultType.NO_CHECK;
                    } else if (hasTaintPaths.isEmpty()) {
                        System.out.println("No-Entry for input url");
                        type = ResultType.NO_ENTRY;
                    } else {
                        // 有的路径可以load，有的不行，这说明存在一定的检查
                        // 查看taintMainVal在condition语句中的存在性
                        if (hasCheckWithTaintVal(ir, valFieldName, symbolTable)) {
                            System.out.println("Has Check for input url");
                            type = ResultType.URL_CHECK;
                        } else {
                            System.out.println("No-entry for input url, but has other check");
                            type = ResultType.OTHER_CHECK;
                        }
                        concatData = getConcatData(symbolTable, allTaintCatVal, concatFieldName);
                    }
                    dumpData(FormatorAndRrcorder.getFileName(pathStr), type, valFieldName, concatData);
                    System.out.println("Finish analyze " + pathStr);
                    return;
                }
            }
        }
    }





}

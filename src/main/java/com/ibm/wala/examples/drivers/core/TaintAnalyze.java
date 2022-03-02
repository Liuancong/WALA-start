package com.ibm.wala.examples.drivers.core;

import com.ibm.wala.cast.ir.ssa.AstGlobalRead;
import com.ibm.wala.cast.ir.ssa.AstGlobalWrite;
import com.ibm.wala.cast.js.ssa.JavaScriptCheckReference;
import com.ibm.wala.cast.js.ssa.JavaScriptInvoke;
import com.ibm.wala.cast.js.ssa.JavaScriptPropertyWrite;
import com.ibm.wala.cast.js.ssa.PrototypeLookup;
import com.ibm.wala.examples.drivers.InvokePath;
import com.ibm.wala.ssa.*;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

public class TaintAnalyze {


    /*
        反向污点分析，获取参数
        污染传播规则: 污染量 = 污染量 + 拼接量 / 污染量 = 污染量.concat(拼接量...) / 污染量 = 污染量
     */
    public static boolean hasTaintFlow(InvokePath path, SymbolTable symbolTable, String targetDataName,
                                       HashSet<Integer> allTaintVal, HashSet<Integer> allTaintCatVal,
                                       HashSet<String> valuableFieldNames, HashSet<String> concatFieldName) {
        // 反向污点分析
        HashSet<Integer> taintedMainVal = new HashSet<>(), taintedConcatVal = new HashSet<>();
        HashSet<String> trackNamesForMain = new HashSet<>(), trackNamesForConcat = new HashSet<>(); // 在Global中特殊的需要track的名称
        // 定义source和sink
        int sink = 3; // 参数1和2没有用
        int source = -100;
        // 记录污点量field访问情况
        HashMap<Integer, String> taintedValToField = new HashMap<>();
        for (int i = path.instructions.size() - 1; i >= 0; i--) {
            // todo more instruction type???
            SSAInstruction instruction = path.instructions.get(i);
            // 先确定逆向污点分析的起点
            if (instruction instanceof JavaScriptInvoke
                    && (symbolTable.isConstant(((JavaScriptInvoke) instruction).getFunction()))
                    && (symbolTable.getConstantValue(((JavaScriptInvoke) instruction).getFunction())).equals("setData")) {
                // 污点分析的起点
                int target = ((JavaScriptInvoke) instruction).getUse(2);
                taintedMainVal.add(target);
                source = target;
                continue;
            }
            // 没有确定终点不分析
            if (source == -100) {
                continue;
            }
            // 对每个instruction进行污点传播
            int def = instruction.getDef();
            if (def == -1 || taintedMainVal.contains(def) || taintedConcatVal.contains(def)) { // 只处理污点变量或者是没有左值的语句
                // 对每种语句进行污点传播
                if (instruction instanceof JavaScriptInvoke) {
                    // 0-函数名，1-函数所属主体，2开始-参数
                    // constrcutor与名称不是常量的处理
                    if (!(symbolTable.isConstant(((JavaScriptInvoke) instruction).getFunction()))) {
                        if (instruction.toString().contains("construct")) {
                            // 向前追溯
                            if (instruction.getNumberOfUses() > 1) {
                                int param = instruction.getUse(1);
                                int type = instruction.getUse(0);
                                for (int ci = 0; ci < i; ci++) {
                                    SSAInstruction tmpIns = path.instructions.get(ci);
                                    if (tmpIns instanceof AstGlobalRead && tmpIns.getDef() == type) {
                                        if (((AstGlobalRead) tmpIns).getGlobalName().contains("URL")) {
                                            if (taintedMainVal.contains(def)) {
                                                taintedMainVal.add(param);
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            System.out.println("Invoke Ins but name is not Constant: " + instruction.toString());
                        }
                        continue;
                    }
                    String funcName = (String) symbolTable.getConstantValue(((JavaScriptInvoke) instruction).getFunction());
                    if (funcName.equals("concat")) {
                        if (taintedMainVal.contains(def)) {
                            taintedMainVal.add(instruction.getUse(1));
                            for (int p = 2; p < instruction.getNumberOfUses(); p++) {
                                taintedConcatVal.add(instruction.getUse(p));
                            }
                        } else {
                            // 对拼接变量的追踪
                            for (int p = 1; p < instruction.getNumberOfUses(); p++) {
                                taintedConcatVal.add(instruction.getUse(p));
                            }
                        }
                    } else if (funcName.startsWith("getStorage")) {
                        if (taintedConcatVal.contains(def)) {
                            taintedConcatVal.add(instruction.getUse(2));
                        }
                    } else if (funcName.toLowerCase().contains("encode") || funcName.toLowerCase().contains("decode")) {
                        if (taintedMainVal.contains(def)) {
                            taintedMainVal.add(instruction.getUse(2));
                        } else {
                            for (int p = 2; p < instruction.getNumberOfUses(); p++) {
                                taintedConcatVal.add(instruction.getUse(p));
                            }
                        }
                    } else {
                        // 对string原型链上的函数做一些特殊分析
                        HashSet<String> funcs = new HashSet<>(Arrays.asList("match", "matchAll", "replace", "replaceAll", "slice", "split",
                                "startsWith", "endsWith", "toLowerCase", "toUpperCase"));
                        if (funcs.contains(funcName)) {
                            if (taintedMainVal.contains(def)) {
                                taintedMainVal.add(instruction.getUse(1));
                            } else {
                                for (int p = 1; p < instruction.getNumberOfUses(); p++) {
                                    taintedConcatVal.add(instruction.getUse(p));
                                }
                            }
                        }
                        // 如果没有参数，同时调用主体不是1或者2，那么调用主体也要进行主变量传递
                        if (instruction.getNumberOfUses() < 3 && instruction.getUse(1) > 2) {
                            taintedMainVal.add(instruction.getUse(1));
                        }
                        // 暂时不分析其他函数（不进行跨函数的追踪）
                    }
                } else if (instruction instanceof SSAGotoInstruction) {
                    // 啥也不干
                } else if (instruction instanceof PrototypeLookup) {
                    if (taintedMainVal.contains(def)) {
                        taintedMainVal.add(instruction.getUse(0));
                        // 记录参数的目标field
                        if (instruction.getUse(0) == sink) {
                            valuableFieldNames.add(taintedValToField.get(def));
                        }
                    } else {
                        taintedConcatVal.add(instruction.getUse(0));
                    }
                } else if (instruction instanceof JavaScriptPropertyWrite) {
                    int leftVal = instruction.getUse(0);
                    int field = instruction.getUse(1);
                    int target = instruction.getUse(2);
                    String fieldName = (String) symbolTable.getConstantValue(field);
                    if (taintedMainVal.contains(leftVal)) {
                        if (leftVal == source) {
                            // 只有和目标field相等的才传播
                            if (fieldName.equals(targetDataName)) {
                                taintedMainVal.add(target);
                            }
                        } else {
                            taintedMainVal.add(target);
                        }
                    } else if (taintedConcatVal.contains(leftVal)) {
                        taintedConcatVal.add(field);
                        taintedConcatVal.add(target);
                    }
                } else if (instruction instanceof JavaScriptCheckReference) {
                    // 啥也不做
                } else if (instruction instanceof AstGlobalRead) {
                    String name = ((AstGlobalRead) instruction).getGlobalName();
                    if (taintedMainVal.contains(def)) {
                        trackNamesForMain.add(name);
                    } else {
                        trackNamesForConcat.add(name);
                    }
                } else if (instruction instanceof AstGlobalWrite) {
                    String name = ((AstGlobalWrite) instruction).getGlobalName();
                    int ta = ((AstGlobalWrite) instruction).getUse(1);
                    if (trackNamesForMain.contains(name)) {
                        taintedMainVal.add(ta);
                    }
                    if (trackNamesForConcat.contains(name)) {
                        taintedConcatVal.add(ta);
                    }
                } else if (instruction instanceof SSAConditionalBranchInstruction) {
                    // 啥也不干
                } else if (instruction.getClass().getName().startsWith("com.ibm.wala.cast.js.loader.JavaScriptLoader$")) {
                    // 特殊的loader语句
                    String ins = instruction.toString();
                    if (instruction.toString().contains("binaryop(add)")) {
                        if (taintedMainVal.contains(def)) {
                            taintedMainVal.add(instruction.getUse(0));
                            taintedConcatVal.add(instruction.getUse(1));
                        } else {
                            taintedConcatVal.add(instruction.getUse(0));
                            taintedConcatVal.add(instruction.getUse(1));
                        }
                    } else if (instruction.toString().contains("getfield")) {
                        // 求field的名称
                        String fieldName = instruction.toString().split(",")[2];
                        if (taintedMainVal.contains(def)) {
                            taintedMainVal.add(instruction.getUse(0));
                            taintedValToField.put(instruction.getUse(0), fieldName);
                        } else {
                            taintedConcatVal.add(instruction.getUse(0));
                            concatFieldName.add(fieldName);
                        }
                    } else if (instruction.toString().contains("new <JavaScriptLoader,LArray>")) {
                        // 啥也不做
                    } else {
                        System.out.println("New type of JavaScriptLoader : " + instruction.toString());
                    }
                } else {
                    String type = instruction.getClass().getName();
                    System.out.println("New Type of instruction: " + type);
                }
            }
        }
        allTaintVal.addAll(taintedMainVal);
        allTaintCatVal.addAll(taintedConcatVal);
        // 判断是否存在source到sink的路径
        return taintedMainVal.contains(sink);
    }


    /*
    正向的污点分析，判断某个field是否会出现在if检查中
     */
    public static boolean hasCheckWithTaintVal(IR ir, String fieldName, SymbolTable symbolTable) {
        int source = 3;
        HashSet<Integer> topLevelValFromParam = new HashSet<>();
        HashSet<Integer> taintedVal = new HashSet<>();
        taintedVal.add(source);
        HashSet<String> taintedName = new HashSet<>();
        HashSet<Integer> excludeTaintVal = new HashSet<>(); // 有些val如果直接出现在if里，可能是一个判空检查，这些不算
        for (SSAInstruction instruction : ir.getInstructions()) {
            if (instruction == null){
                continue;
            }
            // 对每种语句进行正向的污点传播
            if (instruction instanceof JavaScriptInvoke) {
                // 0-函数名，1-函数所属主体，2开始-参数
                // constructor与名称不是常量的处理
                if (!(symbolTable.isConstant(((JavaScriptInvoke) instruction).getFunction()))) {
                    if (instruction.toString().contains("construct")) {
                        // 向前追溯
                        if (instruction.getNumberOfUses() > 1) {
                            int param = instruction.getUse(1);
                            if (taintedVal.contains(param)){
                                taintedVal.add(instruction.getDef());
                            }
                        }
                    } else {
                        System.out.println("Invoke Ins but name is not Constant: " + instruction.toString());
                    }
                    continue;
                }
                // 其他函数调用的处理
                // 如果函数调用主体被污染，那么一定污点
                if (taintedVal.contains(instruction.getUse(1))){
                    taintedVal.add(instruction.getDef());
                    excludeTaintVal.add(instruction.getDef());
                    continue;
                }
                // 如果函数出现在调用参数中，那么也污染上吧
                for (int p = 2; p < instruction.getNumberOfUses(); p++) {
                    if (taintedVal.contains(instruction.getUse(p))){
                        taintedVal.add(instruction.getDef());
                        String funcName = (String) symbolTable.getConstantValue(((JavaScriptInvoke) instruction).getFunction());
                        if (funcName.toLowerCase().contains("empty") || funcName.toLowerCase().contains("format") || funcName.toLowerCase().contains("encode") || funcName.toLowerCase().contains("decode")){
                            excludeTaintVal.add(instruction.getDef());
                        }
                    }
                }
            } else if (instruction instanceof SSAGotoInstruction) {
                // 啥也不干
            } else if (instruction instanceof PrototypeLookup) {
                int base = instruction.getUse(0);
                int res = instruction.getDef();
                if (taintedVal.contains(base)){
                    taintedVal.add(res);
                    excludeTaintVal.add(instruction.getDef());
                    if (base == source){
                        topLevelValFromParam.add(res);
                    }
                }
            } else if (instruction instanceof JavaScriptPropertyWrite) {
                int leftVal = instruction.getUse(0);
                int target = instruction.getUse(2);
                if (taintedVal.contains(target)){
                    taintedVal.add(leftVal);
                }
            } else if (instruction instanceof JavaScriptCheckReference) {
                // 啥也不做
            } else if (instruction instanceof AstGlobalRead) {
                String name = ((AstGlobalRead) instruction).getGlobalName();
                if (taintedName.contains(name)) {
                    taintedVal.add(instruction.getDef());
                }
            } else if (instruction instanceof AstGlobalWrite) {
                String name = ((AstGlobalWrite) instruction).getGlobalName();
                int ta = ((AstGlobalWrite) instruction).getUse(1);
                if (taintedVal.contains(ta)){
                    taintedName.add(name);
                }
            } else if (instruction instanceof SSAConditionalBranchInstruction) {
                int base = instruction.getUse(0);
                int compare = instruction.getUse(1);
                if (taintedVal.contains(base) && !excludeTaintVal.contains(base)){
                    return true;
                }
                if (taintedVal.contains(compare) && !excludeTaintVal.contains(compare)){
                    return true;
                }
            } else if (instruction.getClass().getName().startsWith("com.ibm.wala.cast.js.loader.JavaScriptLoader$")) {
                // 特殊的loader语句
                String ins = instruction.toString();
                if (ins.contains("binaryop")) {
                    if (taintedVal.contains(instruction.getUse(0)) || taintedVal.contains(instruction.getUse(1))){
                        taintedVal.add(instruction.getDef());
                    }
                } else if (ins.contains("getfield")) {
                    // 求field的名称
                    String name = instruction.toString().split(",")[2];
                    if (taintedVal.contains(instruction.getUse(0))){
                        if (topLevelValFromParam.contains(instruction.getUse(0))){
                            if (name.equals(fieldName)){
                                taintedVal.add(instruction.getDef());
                                excludeTaintVal.add(instruction.getDef());
                            }
                        } else {
                            taintedVal.add(instruction.getDef());
                            excludeTaintVal.add(instruction.getDef());
                        }
                    }
                } else if (ins.contains("new <JavaScriptLoader,LArray>")) {
                    // 啥也不做
                } else {

                }
            } else {

            }

        }
        return false;
    }


}

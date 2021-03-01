package com.toposat;

import java.io.*;
import java.util.HashSet;

public class TseytinTransformation {
    // if TypeOperation is an operation, not a variable or undefined or parentheses
    public static boolean isOperation(TypeOperation t){
        return ((t != TypeOperation.undefined) &&
                (t != TypeOperation.open) &&
                (t != TypeOperation.close) &&
                (t != TypeOperation.variable));
    }

    // String representation to TypeOperation
    public static TypeOperation getOpType(String str){
        if(str == null){return TypeOperation.undefined; }
        if(str.equals("")){return TypeOperation.undefined;}
        if(str.equals("&&")){return TypeOperation.conjunction;}
        if(str.equals("||")){ return TypeOperation.disjunction;}
        if(str.equals("!")){return TypeOperation.not;}
        if(str.equals("->")){return TypeOperation.implication;}
        if(str.equals("<->")){return TypeOperation.equivalence;}
        if(str.equals("(")){return TypeOperation.open;}
        if(str.equals(")")){return TypeOperation.close;}
        if(str.equals("+")){return TypeOperation.xor;}
        return TypeOperation.variable;
    }

    //TypeOperation to String representation
    public static String getOpSymbol(TypeOperation t){
        if(t == TypeOperation.undefined){return "";}
        if(t == TypeOperation.conjunction){return "&&";}
        if(t == TypeOperation.disjunction){ return "||";}
        if(t == TypeOperation.not){return "!";}
        if(t == TypeOperation.implication){return "->";}
        if(t == TypeOperation.equivalence){return "<->";}
        if(t == TypeOperation.open){return "(";}
        if(t == TypeOperation.close){return ")";}
        if(t == TypeOperation.variable){return "";}
        if(t == TypeOperation.xor){return "+";}
        return "";
    }

    // creates formula tree from a split text formula
    public static int makeTree(String[] formula, int start, int stop, com.toposat.NodeFormula root){
        int pos = start;
        if(stop - start <= 0){
            return 1;
        }
        if(stop - start == 1){
            if(getOpType(formula[pos]) == TypeOperation.variable){
                root.operation = TypeOperation.variable;
                root.varName = formula[pos];
                return 0;
            } else {
                System.out.println("Error occurred");
                return 2;
            }
        }
        if(getOpType(formula[start]) == TypeOperation.not){
            root.operation =  getOpType(formula[pos]);
            root.left = new com.toposat.NodeFormula();
            root.right = null;
            makeTree(formula, start + 1, stop, root.left);
            return 0;
        }
        int openCnt = 0;
        int closeCnt = 0;
        for(; pos < stop; ++pos){
            TypeOperation op = getOpType(formula[pos]);
            if(op == TypeOperation.open){
                ++openCnt;
            }
            if(op == TypeOperation.close){
                ++closeCnt;
            }
            if(isOperation(op)){
                if(openCnt == closeCnt){
                    root.operation = op;
                    root.left = new com.toposat.NodeFormula();
                    root.right = new com.toposat.NodeFormula();
                    int a = makeTree(formula, start, pos, root.left);
                    if(a != 0){
                        root.left = null;
                    }
                    if(a == 2){
                        return 2;
                    }
                    a = makeTree(formula, pos + 1, stop, root.right);
                    if(a != 0){
                        root.right = null;
                    }
                    if(a == 2){
                        return 2;
                    }
                    return 0;
                }
            }
        }
        if(openCnt == closeCnt && getOpType(formula[start]) == TypeOperation.open &&
                getOpType(formula[stop-1]) == TypeOperation.close){
            makeTree(formula, start + 1, stop - 1, root);
        }
        if(openCnt != closeCnt){
            System.out.println("Error occurred: Parentheses don't match.");
            return 2;
        }
        return 0;
    }

    // creates additional variables, which are needed for transformation
    // they have a name? dut not an id
    private static int addVariables(com.toposat.NodeFormula root, int start){
        if(root == null){
            return start;
        }
        if(isOperation(root.operation)){
            root.addVar = "added" + start;
            ++start;
        }
        int left = addVariables(root.left, start);
        return addVariables(root.right, left);
    }

    // writes formula tree, just for checking
    static void TsTreeWalk(com.toposat.NodeFormula root, FileWriter Writer, int shift) throws IOException {
        if(root == null){
            return;
        }
        for(int i = 0; i < shift; ++i){
            Writer.write(" ");
        }
        Writer.write("operation = " + root.operation + " addVar = " + root.addVar + " varName = " + root.varName + "\n");
        for(int i = 0; i <shift; ++i){
            Writer.write(" ");
        }
        Writer.write("left:\n");
        TsTreeWalk(root.left, Writer, shift + 1);
        for(int i = 0; i <shift; ++i){
            Writer.write(" ");
        }
        Writer.write("right:\n");
        TsTreeWalk(root.right, Writer, shift + 1);
    }

    // these functions add CNF clauses(according to possible types of operations) to a new tree for CNF

    private static void transformCon(com.toposat.NodeFormula newRoot, String C, String A, String B){
        String newFormula = "( ( ! " + A + " ) || ( ! " + B + " ) || " + C +
                " ) && ( " + A + " || ( ! " + C +
                " ) ) && ( "  + B + " || ( ! " + C + " ) )";
        System.out.println(newFormula);
        String[] str = newFormula.trim().split("\\s+");
        makeTree(str, 0, str.length, newRoot);
    }
    private static void transformDis(com.toposat.NodeFormula newRoot, String C, String A, String B){
        String newFormula = "( " + A + " || " + B + " || ( ! " + C +
                " ) ) && ( ( ! " + A + " ) || "  + C +
                " ) && ( ( ! " + B + " ) || " + C + " )";
        System.out.println(newFormula);
        String[] str = newFormula.trim().split("\\s+");
        makeTree(str, 0, str.length, newRoot);
    }
    private static void transformNot(com.toposat.NodeFormula newRoot, String C, String A){
        String newFormula = "( ( ! " + A + " ) || ( ! " + C +
                " ) ) && ( " + A + " || " + C + " )";
        System.out.println(newFormula);
        String[] str = newFormula.trim().split("\\s+");
        makeTree(str, 0, str.length, newRoot);
    }
    private static void transformImpl(com.toposat.NodeFormula newRoot, String C, String A, String B){
        String newFormula = "( " + A + " || " + B + " || " + C +
                " ) && ( " + A + " || ( ! " + B + " ) || " + C +
                " ) && ( ( ! " + A + " ) || ( ! " + B + " ) || " + C +
                " ) &&  ( ( ! " + A + " ) || ( ! " + B + " ) || ( ! " + C +
                " ) )";
        System.out.println(newFormula);
        String[] str = newFormula.trim().split("\\s+");
        makeTree(str, 0, str.length, newRoot);
    }
    private static void transformEquiv(com.toposat.NodeFormula newRoot, String C, String A, String B){
        String newFormula = "( " + A + " || ( ! " + B + " ) || ( ! " + C +
                " ) ) && ( ( ! " + A + " ) || " + B + " || ( ! " + C +
                " ) ) && ( ( ! " + A + " ) || ( ! " + B + " ) || " + C +
                " ) && ( " + A + " || " + B + " || " + C +
                " )";
        System.out.println(newFormula);
        String[] str = newFormula.trim().split("\\s+");
        makeTree(str, 0, str.length, newRoot);
    }
    private static void transformXor(com.toposat.NodeFormula newRoot, String C, String A, String B){
        String newFormula = "( ( ! " + A + " ) || ( ! " + B + " ) || ( ! " + C +
                " ) ) && ( " + A + " || " + B + " || ( ! " + C +
                " ) ) && ( " + A + " || ( ! " + B + " ) || " + C +
                " ) && ( ( ! " + A + " ) || " + B + " || " + C +
                " )";
        System.out.println(newFormula);
        String[] str = newFormula.trim().split("\\s+");
        makeTree(str, 0, str.length, newRoot);
    }

    // gets a place for a new node in formula tree
    static com.toposat.NodeFormula findPlace(com.toposat.NodeFormula root){
        if(root == null){
            root = new com.toposat.NodeFormula();
            root.operation = TypeOperation.conjunction;
            return root;
        }
        if(root.left == null){
            root.left = new com.toposat.NodeFormula();
            root.left.operation = TypeOperation.conjunction;
            return root.left;
        } else if(root.right == null){
            root.right = new com.toposat.NodeFormula();
            root.right.operation = TypeOperation.conjunction;
            return root.right;
        } else {
            com.toposat.NodeFormula curr = root.left;
            root.left = new com.toposat.NodeFormula();
            root.left.left = curr;
            root.left.operation = TypeOperation.conjunction;
            root.left.right = new com.toposat.NodeFormula();
            root.left.right.operation = TypeOperation.conjunction;
            return root.left.right;
        }
    }

    // calls transforming functions for all operation nodes according to type
    private static void transformToCNF(com.toposat.NodeFormula root, com.toposat.NodeFormula newRoot){
        if((root == null) || (root.operation == TypeOperation.variable)){
            return;
        }
        if(!isOperation(root.operation)){
            return;
        }
        if((root.left == null) && (root.right == null)){
            System.out.println("here");
            return;
        }
        com.toposat.NodeFormula place = findPlace(newRoot);
        String C = root.addVar;
        String A , B ="";
        TypeOperation t = root.operation;
        if(root.left.operation == TypeOperation.variable){
            A = root.left.varName;
        } else {
            A = root.left.addVar;
        }
        if(t != TypeOperation.not){
            if(root.right.operation == TypeOperation.variable){
                B = root.right.varName;
            } else {
                B = root.right.addVar;
            }
        }
        if(t == TypeOperation.conjunction){transformCon(place, C, A, B);}
        if(t == TypeOperation.disjunction){transformDis(place, C, A, B);}
        if(t == TypeOperation.not){transformNot(place, C, A);}
        if(t == TypeOperation.implication){transformImpl(place, C, A, B);}
        if(t == TypeOperation.equivalence){transformEquiv(place, C, A, B);}
        if(t == TypeOperation.xor){transformXor(place, C, A, B);}
        transformToCNF(root.right, newRoot);
        transformToCNF(root.left, newRoot);
    }

    public static void startTransformationCNF(com.toposat.NodeFormula root, com.toposat.NodeFormula newRoot) {
        addVariables(root, 0);
        newRoot.operation = TypeOperation.conjunction;
        newRoot.right = new com.toposat.NodeFormula();
        newRoot.right.operation = TypeOperation.variable;
        newRoot.right.varName = root.addVar;
        newRoot.left = new com.toposat.NodeFormula();
        newRoot = newRoot.left;
        transformToCNF(root, newRoot);
    }

    static private void writeClauseSMT(com.toposat.NodeFormula root, FileWriter Writer, int start) throws IOException {
        if(root == null){
            return;
        }
        if(start == 1){
            Writer.write("(assert (or ");
        }

        if(root.operation == TypeOperation.not){
            Writer.write("(not ");
            writeClauseSMT(root.left, Writer, 0);
            writeClauseSMT(root.right, Writer, 0);
            Writer.write(") ");
            return;
        }
        if(root.operation == TypeOperation.variable){
            Writer.write(root.varName + " ");
            return;
        }
        writeClauseSMT(root.left, Writer, 0);
        writeClauseSMT(root.right, Writer, 0);
        if(start == 1){
            Writer.write("))\n");
        }
    }

    static private void treeWalkSMT(com.toposat.NodeFormula root, FileWriter Writer) throws IOException {
        if(root == null){
            return;
        }
        if(root.operation == TypeOperation.disjunction){
            writeClauseSMT(root, Writer, 1);
            return;
        }
        if(root.operation == TypeOperation.variable){
            Writer.write("(assert " + root.varName + " )\n");
        }
        treeWalkSMT(root.left, Writer);
        treeWalkSMT(root.right, Writer);
    }

    static private HashSet<String> declareVariablesSMT(com.toposat.NodeFormula root, FileWriter Writer, HashSet<String> varNames) throws IOException {
        if(root == null){
            return varNames;
        }
        if(root.varName != null){
            if(!varNames.contains(root.varName)){
                varNames.add(root.varName);
                if(root.varName == null){
                    System.out.println("root.var = " + root.var);
                }
                Writer.write("(declare-const " + root.varName + " Bool)\n");
            }
            return varNames;
        }
        varNames = declareVariablesSMT(root.left, Writer, varNames);
        varNames = declareVariablesSMT(root.right, Writer,varNames);
        return varNames;
    }
    // writes CNF formula in SMT format in file filename(which is created)
    static void writeSmtCNF(com.toposat.NodeFormula root, String filename) {
        try {
            File formulaFile = new File(filename);
            formulaFile.createNewFile();
            FileWriter Writer = new FileWriter(filename);
            numberVariables nv = new numberVariables();
            nv.declareVariablesSMT(root, Writer);
            treeWalkSMT(root, Writer);
            Writer.write("(check-sat)\n");
            Writer.write("(get-model)\n");
            Writer.close();
        } catch (IOException e) {
            System.out.println("An error occured.");
            e.printStackTrace();
        }
    }

    // reads input file and splits by whitespace
    public static String[] formulaFromFile(String filePath){
        String str = "";
        try {
            File file = new File(filePath);
            FileReader fr = new FileReader(file);
            BufferedReader br = new BufferedReader(fr);
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) {
                sb.append(line);
                sb.append(" ");
            }
            fr.close();
            str = sb.toString();
            return str.trim().split("\\s+");
        }
        catch(IOException e){
            e.printStackTrace();
        }
        return str.trim().split("\\s+");
    }

    // gets in arguments the path to the file containing boolean formula, the formula must be written according to format to work correctly
    // All operations and variables must be divided by whitespace, (! A && B ) is not ( ! A ) && B,  (! A && B) is  ! ( A && B )
    public static void main(String[] args){
        try {
            String filePath;
            filePath = args[0];
            //filePath = "/home/nastya/Documents/java/Demo.txt";
            String[] split = formulaFromFile(filePath);

            com.toposat.NodeFormula root = new com.toposat.NodeFormula();
            makeTree(split, 0, split.length, root);
            FileWriter Writer = new FileWriter("treeFile.txt");
            TsTreeWalk(root, Writer, 0);
            Writer.close();

            com.toposat.NodeFormula place = new NodeFormula();
            place.operation = TypeOperation.conjunction;
            startTransformationCNF(root, place);
            transformToCNF(root, place);
            FileWriter WriterNew = new FileWriter("newTreeFile.txt");
            TsTreeWalk(place, WriterNew, 0);
            WriterNew.close();

        }
        catch(IOException e){
            e.printStackTrace();
        }

    }
}
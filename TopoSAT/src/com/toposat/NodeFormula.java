package com.toposat;

public class NodeFormula { // node in cnf
    public TypeOperation operation = TypeOperation.undefined; // just some default value
    int var; // variable id
    public String varName; // used in writing formula to SMT, if not defined...
    public NodeFormula left; // left child
    public NodeFormula right; // right child
    public String addVar; // additional variable
}
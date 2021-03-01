package com.toposat;

import org.jgrapht.Graph;

public interface VisitorGraphToFormula extends Visitor{
    com.toposat.NodeFormula m_resFormula = null;
    //void setFormulaOutput();
    void visitNode(com.toposat.NodeFormula curr, NVertex vertex, Graph<NVertex, NEdge> graph);
    void visitEdge(com.toposat.NodeFormula curr, NEdge edge, Graph<NVertex, NEdge> graph);
    void visitGraph(com.toposat.NodeFormula curr, Graph<NVertex, NEdge> graph);
    void visitNonEdge(com.toposat.NodeFormula curr, NVertex first, NVertex second, Graph<NVertex, NEdge> graph);
}

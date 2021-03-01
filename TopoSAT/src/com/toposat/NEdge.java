package com.toposat;

import org.jgrapht.graph.DefaultEdge;

public class NEdge  extends DefaultEdge {
    private final String label; // label
    private final int id;
    private final int reverseId;

    public NEdge(String label, int id, int reverseId) {
        this.label = label;
        this.id = id;
        this.reverseId = reverseId;
    }
    public int getReverseId(){ return this.reverseId; }
    public String getLabel(){
        return this.label;
    }
    public int getId(){
        return this.id;
    }
    public String toString(){
        return "NEdge" + id + label;
    }
    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    public NVertex getFirst() {
        return (NVertex) this.getSource();
    }
    public NVertex getSecond() {
        return (NVertex) this.getTarget();
    }

    @Override
    public boolean equals(Object obj) {
        boolean result;
        if (obj == this) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (obj.getClass() != String.class) {
            if (obj.getClass() != this.getClass()) {
                return false;
            }
            NEdge v = (NEdge) obj;
            result = (this.id == (v.getId()));
        } else {
            String s = (String) obj;
            result = this.toString().equals(s);
        }
        return result;
    }
}
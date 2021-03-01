package com.toposat;

public class NVertex {
    private final String label; // label - String id
    private final int id;
    private final String name; // another label

    public NVertex(String label, int id, String name) {
        this.label = label;
        this.id = id;
        this.name = name;
    }
    public String getLabel(){ return label; }
    public int getId(){ return id; }
    public String getName(){ return name; }
    public String toString(){ return "NVertex" + id + label; }
    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }
    @Override
    public boolean equals(Object obj){
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
            NVertex v = (NVertex) obj;
            result = (this.id == (v.getId()));
        }
        else {
            String s = (String) obj;
            result = this.toString().equals(s);
        }
        return result;
    }
}
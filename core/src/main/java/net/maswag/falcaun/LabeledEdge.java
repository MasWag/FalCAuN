package net.maswag.falcaun;

import org.jgrapht.graph.*;
import org.jgrapht.nio.*;

import java.util.*;

public class LabeledEdge extends DefaultEdge {
    private Map<String, Set<Attribute>> attrs;

    public LabeledEdge() {
        attrs = new HashMap<>();
    }

    public void setAttrs(Map<String, Attribute> map) {
        for (String key : map.keySet()){
            Attribute attr = map.get(key);
            if (attrs.containsKey(key)) {
                attrs.get(key).add(attr);
            } else {
                Set<Attribute> attrSet = new HashSet<>();
                attrSet.add(attr);
                attrs.put(key, attrSet);
            }
        }
        return;
    }

    public String getAttr() {
        return attrs.get("label").toString();
    }

    public boolean isAtrrNull() {
        return attrs.isEmpty();
    }

    @Override
    public String getSource() {
        return super.getSource().toString();
    }

    @Override
    public String getTarget() {
        return super.getTarget().toString();
    }

    @Override
    public String toString()
    {
        return "(" + getSource() + " : " + getTarget() + ")" + attrs.get("label");
    }
}
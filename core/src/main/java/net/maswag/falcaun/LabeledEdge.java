package net.maswag.falcaun;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.nio.Attribute;

public class LabeledEdge extends DefaultEdge {
    private final Map<String, Attribute> attrs;

    public LabeledEdge() {
        attrs = new HashMap<>();
    }

    public void setAttrs(Map<String, Attribute> map) {
        attrs.clear();
        attrs.putAll(map);
    }

    public Optional<String> getAttr() {
        Attribute label = attrs.get("label");
        return label == null ? Optional.empty() : Optional.of(label.getValue());
    }

    public boolean isAttrNull() {
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
        String label = getAttr().orElse("");
        return "(" + getSource() + " : " + getTarget() + ")" + label;
    }
}

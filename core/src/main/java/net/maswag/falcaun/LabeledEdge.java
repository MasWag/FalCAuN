package net.maswag.falcaun;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.nio.Attribute;
import org.jgrapht.nio.AttributeType;

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
        return getAttr()
            .map(value -> "(" + getSource() + " : " + getTarget() + ")" + "[" + value + "]")
            .orElse("(" + getSource() + " : " + getTarget() + ")" + "null");
    }

    /**
     * Convenience factory for string attributes.
     */
    public static Attribute stringAttribute(String value) {
        return new Attribute() {
            @Override
            public String getValue() {
                return value;
            }

            @Override
            public AttributeType getType() {
                return AttributeType.STRING;
            }
        };
    }
}

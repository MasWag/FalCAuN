package net.maswag.falcaun;

import java.util.Objects;
import java.util.Optional;

public class LabeledEdge {
    private final String source;
    private final String target;
    private String label;

    public LabeledEdge(String source, String target) {
        this.source = source;
        this.target = target;
    }

    public void setLabel(String label) {
        this.label = label;
    }

    public Optional<String> getAttr() {
        return Optional.ofNullable(label);
    }

    public boolean isAttrNull() {
        return label == null;
    }

    public String getSource() {
        return source;
    }

    public String getTarget() {
        return target;
    }

    @Override
    public String toString()
    {
        return getAttr()
            .map(value -> "(" + getSource() + " : " + getTarget() + ")" + "[" + value + "]")
            .orElse("(" + getSource() + " : " + getTarget() + ")" + "null");
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) { return true; }
        if (!(o instanceof LabeledEdge)) { return false; }
        LabeledEdge that = (LabeledEdge) o;
        return Objects.equals(source, that.source)
            && Objects.equals(target, that.target)
            && Objects.equals(label, that.label);
    }

    @Override
    public int hashCode() {
        return Objects.hash(source, target, label);
    }
}

package org.group_mmm;

public class SimulinkAbstractAlphabetDomain {
    private String rawValue;

    public SimulinkAbstractAlphabetDomain(String rawValue) {
        this.rawValue = rawValue;
    }

    public String getRawValue() {
        return rawValue;
    }

    public int toInt() {
        return rawValue.hashCode();
    }
}

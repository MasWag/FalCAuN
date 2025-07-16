package net.maswag.falcaun.simulink;

/**
 * <p>SimulinkAbstractAlphabetDomain class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class SimulinkAbstractAlphabetDomain {
    private String rawValue;

    /**
     * <p>Constructor for SimulinkAbstractAlphabetDomain.</p>
     *
     * @param rawValue a {@link java.lang.String} object.
     */
    public SimulinkAbstractAlphabetDomain(String rawValue) {
        this.rawValue = rawValue;
    }

    /**
     * <p>Getter for the field <code>rawValue</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getRawValue() {
        return rawValue;
    }

    /**
     * <p>toInt.</p>
     *
     * @return a int.
     */
    public int toInt() {
        return rawValue.hashCode();
    }
}

package net.maswag.falcaun;

import lombok.Getter;
import lombok.Setter;

/**
 * Base class for LTL formula implementations that provides common functionality
 * for atomic propositions management using composition instead of inheritance.
 * This class is used by LTL inner classes that need to extend their parent temporal classes.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class LTLFormulaBase {
    @Getter
    @Setter
    private LTLAPs aps;
    
    /**
     * Sets the atomic propositions and propagates them to subformulas.
     * 
     * @param aps The atomic propositions to set
     * @param propagator A runnable that propagates the APs to subformulas
     */
    public void setAPsWithPropagation(LTLAPs aps, Runnable propagator) {
        this.aps = aps;
        if (propagator != null) {
            propagator.run();
        }
    }
}
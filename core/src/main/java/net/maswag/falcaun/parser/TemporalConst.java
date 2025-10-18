package net.maswag.falcaun.parser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;

public class TemporalConst<I> extends AbstractTemporalLogic<I>{
    private final boolean condition;

    TemporalConst(boolean b){
        this.condition = b;
        this.iOType = IOType.BOTH;
    }

    @Override
    public String toAbstractString(){
        if (condition) { return "true";}
        else {return "false";}
    }

    @Override
    public String toString(){
        return toAbstractString();
    }

    @Override
    public String toOwlString(){
        if (condition) { return "true"; }
        else { return "false"; }
    }

    /**
     * <p>getRoSI.</p>
     *
     * @return a {@link RoSI} object.
     */
    public RoSI getRoSI(IOSignal<I> signal){
        if (condition) { return new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY); }
        else { return new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY); }
    }

    @Override
    public Set<String> getAllAPs(){
        return new HashSet<>();
    }

    public TemporalLogic<I> derivativeOn(String c){
        return this;
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate){
        if (negate){
            return new TemporalConst<>(!condition);
        } else {
            return new TemporalConst<>(condition);
        }
    }

    public TemporalLogic<I> toDisjunctiveForm(){
        return this;
    }

    public List<TemporalLogic<I>> getAllConjunctions(){
        return new ArrayList<>();
    }

    static class STLConst extends TemporalConst<List<Double>> implements STLCost {
        STLConst(boolean b) {
            super(b);
        }
    }
    
    static class LTLConst extends TemporalConst<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();
        LTLConst(boolean b) {
            super(b);
        }

        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAps(aps);
        }

        @Override
        public LTLAPs getAPs() {
            return formulaBase.getAps();
        }

        @Override
        public void collectAtomicPropositions(LTLAPs aps) {
        }
    }
}

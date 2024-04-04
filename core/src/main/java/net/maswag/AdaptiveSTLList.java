package net.maswag;

import lombok.extern.slf4j.Slf4j;

import java.util.*;
import java.util.function.Function;

/**
 * Adaptive updater of STL/LTL formulas
 *
 * @author Junya Shijubo
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
@Slf4j
public class AdaptiveSTLList<I> extends AbstractAdaptiveSTLUpdater<I> {
    private final List<TemporalLogic<I>> initialSTLs; // list of initial STL formulas
    private final List<TemporalLogic<I>> targetSTLs; // list of STL formulas that are targets of falsification
    private final List<List<TemporalLogic<I>>> strengthenedSTLProperties; // list of strengthened STL formulas for each target STL

    // list of strengthened STLs generated by statically rewriting operators of each target STL
    private final List<List<TemporalLogic<I>>> candidateSTLProperties;
    // list of strengthened STLs generated by adaptively changing intervals of each target STL
    private final List<List<IntervalTL<I>>> intervalSTLProperties;
    // list of STLs that are falsified during BBC
    private final List<TemporalLogic<I>> falsifiedSTLProperties;
    // time window of adaptive STL update
    private final int timeWindow;

    public AdaptiveSTLList() {
        this(Collections.emptySet());
    }

    public AdaptiveSTLList(TemporalLogic<I> propertyOracle) {
        this(Collections.singleton(propertyOracle));
    }

    public AdaptiveSTLList(Collection<? extends TemporalLogic<I>> STLProperties) {
        // Use the default duration
        this(STLProperties, 30);
    }

    /**
     * @param STLProperties The list of STL/LTL formulas to verify
     * @param timeWindow    The maximum time window of the STL formulas. This is typically the number of steps in each simulation.
     */
    public AdaptiveSTLList(Collection<? extends TemporalLogic<I>> STLProperties, int timeWindow) {
        // save original STL formulas to recover when BBC is finished
        this.initialSTLs = new ArrayList<>(STLProperties);
        // target STL/LTL formulas to adaptively strengthen
        this.targetSTLs = new ArrayList<>(STLProperties);
        this.timeWindow = timeWindow;

        // list of strengthened STL/LTL formulas to be model-checked
        this.strengthenedSTLProperties = new ArrayList<>();
        this.candidateSTLProperties = new ArrayList<>();
        this.intervalSTLProperties = new ArrayList<>();
        for (int targetIdx = 0; targetIdx < targetSTLs.size(); targetIdx++) {
            // syntactically strengthen targetSTLs
            this.strengthenedSTLProperties.add(new ArrayList<>());
            this.candidateSTLProperties.add(generateStrengthenedSTL(targetSTLs.get(targetIdx)));
            if (!this.candidateSTLProperties.get(targetIdx).isEmpty()) {
                // if there exists any candidate, add one to STLProperties and model-check against it.
                this.strengthenedSTLProperties.get(targetIdx).add(0, this.candidateSTLProperties.get(targetIdx).remove(0));
            }
            // change intervals of temporal operators in targetSTL
            this.intervalSTLProperties.add(initializeIntervalSTLproperties(targetSTLs.get(targetIdx)));
            for (int j = 0; j < this.intervalSTLProperties.get(targetIdx).size(); j++) {
                this.strengthenedSTLProperties.get(targetIdx).add(j, intervalSTLProperties.get(targetIdx).get(j).strengthInit());
            }
        }

        this.falsifiedSTLProperties = new ArrayList<>();

        this.strengthenedSTLProperties.forEach(this::addSTLProperties);
        this.addSTLProperties(this.targetSTLs);
        log.debug("STLProperties ::=");
        this.getSTLProperties().forEach(s -> log.debug("STL: " + s.toString()));
    }

    /**
     * syntactically strengthen an STL/LTL formula
     *
     * @param stl a target STL formula to be strengthen
     * @return list of {@link TemporalLogic<I>} objects
     */
    private List<TemporalLogic<I>> strengthenSTL(TemporalLogic<I> stl) {
        if (stl instanceof TemporalOr) {
            List<TemporalLogic<I>> subFmls = ((TemporalOr<I>) stl).getSubFmls();
            List<TemporalLogic<I>> ret = new ArrayList<>();
            ret.add(new TemporalAnd<>(subFmls.get(0), subFmls.get(1)));

            strengthenSTL(subFmls.get(0)).forEach(s -> ret.add(new TemporalOr<>(s, subFmls.get(1))));
            strengthenSTL(subFmls.get(1)).forEach(s -> ret.add(new TemporalOr<>(subFmls.get(0), s)));
            return ret;
        }
        if (stl instanceof TemporalAnd) {
            List<TemporalLogic<I>> subFmls = ((TemporalAnd<I>) stl).getSubFormulas();
            List<TemporalLogic<I>> ret = new ArrayList<>();

            strengthenSTL(subFmls.get(0)).forEach(s -> ret.add(new TemporalAnd<>(s, subFmls.get(1))));
            strengthenSTL(subFmls.get(1)).forEach(s -> ret.add(new TemporalAnd<>(subFmls.get(0), s)));
            return ret;
        }
        if (stl instanceof TemporalGlobally) {
            TemporalLogic<I> subFml = ((TemporalGlobally<I>) stl).getSubFml();
            List<TemporalLogic<I>> ret = new ArrayList<>();
            strengthenSTL(subFml).forEach(s -> ret.add(new TemporalGlobally<>(s)));
            return ret;
        }
        if (stl instanceof TemporalUntil) {
            TemporalLogic<I> subFmlLeft = ((TemporalUntil<I>) stl).getLeft();
            TemporalLogic<I> subFmlRight = ((TemporalUntil<I>) stl).getRight();

            return new ArrayList<>(Arrays.asList(
                    new TemporalAnd<>(new TemporalGlobally<>(subFmlLeft), new TemporalGlobally<>(subFmlRight)),
                    new TemporalAnd<>(new TemporalGlobally<>(subFmlLeft), new TemporalEventually<>(new TemporalGlobally<>(subFmlRight))),
                    new TemporalAnd<>(new TemporalGlobally<>(subFmlLeft), new TemporalGlobally<>(new TemporalEventually<>(subFmlRight)))
            ));
        }
        if (stl instanceof TemporalEventually) {
            TemporalLogic<I> subFml = ((TemporalEventually<I>) stl).getSubFml();
            return new ArrayList<>(Arrays.asList(
                    new TemporalGlobally<>(subFml),
                    new TemporalEventually<>(new TemporalGlobally<>(subFml)),
                    new TemporalGlobally<>(new TemporalEventually<>(subFml))
            ));
        }
        return Collections.emptyList();
    }


    /**
     * Notify that subset of this.getLTLProperties are falsified by the currently learned model.
     *
     * @param falsifiedIndices The set of indices of the falsified LTL formulas
     */
    @Override
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
        // remove all STL/LTL formula that is falsified from STLProperties
        falsifiedIndices.sort(Collections.reverseOrder());
        List<TemporalLogic<I>> falsifiedSTLs = new ArrayList<>();
        List<Integer> removedIndices = new ArrayList<>();
        for (int falsifiedIdx : falsifiedIndices) {
            TemporalLogic<I> falsifiedSTL = this.getSTLProperties().get(falsifiedIdx);
            // We remove the STL formula only if it is not an initial formula.
            if (!initialSTLs.contains(falsifiedSTL)) {
                removedIndices.add(falsifiedIdx);
            }
            this.falsifiedSTLProperties.add(falsifiedSTL);
            falsifiedSTLs.add(falsifiedSTL);
        }
        this.removeSTLProperties(removedIndices);

        // if any targetSTL is falsified, remove all strengthened properties generated from the STL
        falsifiedIndices.sort(Collections.reverseOrder());
        for (TemporalLogic<I> falsifiedSTL : falsifiedSTLs) {
            boolean isTarget = false;
            for (int targetIdx = this.targetSTLs.size() - 1; targetIdx >= 0; targetIdx--) {
                if (falsifiedSTL.equals(targetSTLs.get(targetIdx))) {
                    // if a targetSTL is falsified, remove it
                    isTarget = true;
                    log.info("STLProperty is falsified: " + falsifiedSTL);
                    this.targetSTLs.remove(targetIdx);
                    this.candidateSTLProperties.remove(targetIdx);
                    this.intervalSTLProperties.remove(targetIdx);
                    this.strengthenedSTLProperties.remove(targetIdx);
                    if (this.targetSTLs.size() == 0) {
                        log.info("All STLProperties are falsified");
                        return;
                    }
                }
            }
            if (!isTarget) {
                // when the falsifiedSTL is a strengthened property
                log.debug("Adaptive STLProperty is falsified: " + falsifiedSTL);
                for (int targetIdx = 0; targetIdx < this.strengthenedSTLProperties.size(); targetIdx++) {
                    int pos = this.strengthenedSTLProperties.get(targetIdx).indexOf(falsifiedSTL);
                    if (pos != -1) {
                        this.strengthenedSTLProperties.get(targetIdx).remove(pos);
                        if (pos < this.intervalSTLProperties.get(targetIdx).size()) {
                            // if the falsified formula is generated by changing intervals, change intervals to make it stronger
                            TemporalLogic<I> next = this.intervalSTLProperties.get(targetIdx).get(pos).nextStrengthenedSTL();
                            if (Objects.isNull(next)) {
                                this.intervalSTLProperties.get(targetIdx).remove(pos);
                            } else {
                                this.strengthenedSTLProperties.get(targetIdx).add(pos, next);
                                log.debug("Adaptive STLProperty(interval) is added: " + next);
                            }
                        } else {
                            // pick a next STL/LTL formula from candidateSTLProperties
                            if (this.candidateSTLProperties.get(targetIdx).size() > 0) {
                                TemporalLogic<I> newSTL = nextStrengthenedSTL(targetIdx);
                                this.strengthenedSTLProperties.get(targetIdx).add(pos, newSTL);
                                log.debug("Adaptive STLProperty(other) is added: " + newSTL.toString());
                            }
                        }
                    }
                }
            }

        }

        this.strengthenedSTLProperties.forEach(this::addSTLProperties);
        log.debug("Adaptive STLproperties ::");
        this.getSTLProperties().forEach(s -> log.debug("STL: " + s.toString()));
    }

    /**
     * generate syntactically strengthened STL formulas
     *
     * @param targetStl a target STL/LTL formula
     * @return list of strengthened formulas
     */
    private List<TemporalLogic<I>> generateStrengthenedSTL(TemporalLogic<I> targetStl) {
        return strengthenSTL(targetStl);
    }

    /**
     * list up intervals of temporal operators in target STL formulas that can be strengthened
     *
     * @param targetSTL a target STL/LTL formula
     * @return list of
     */
    private List<IntervalTL<I>> initializeIntervalSTLproperties(TemporalLogic<I> targetSTL) {
        return findIntervalSTL(targetSTL, (s) -> s);
    }

    /**
     * find intervals that can be strengthened
     *
     * @param stl   target STL formula
     * @param frame outer frame of param 'stl'
     * @return list of {@link IntervalTL} object
     */
    private List<IntervalTL<I>> findIntervalSTL(TemporalLogic<I> stl, Function<TemporalLogic<I>, TemporalLogic<I>> frame) {
        // search STLSub and STLNext recursively
        if (stl instanceof TemporalOr) {
            List<TemporalLogic<I>> subFmls = ((TemporalOr<I>) stl).getSubFmls();
            List<IntervalTL<I>> ret = new ArrayList<>();

            ret.addAll(findIntervalSTL(subFmls.get(0), (s) -> frame.apply(new TemporalOr<>(s, subFmls.get(1)))));
            ret.addAll(findIntervalSTL(subFmls.get(1), (s) -> frame.apply(new TemporalOr<>(subFmls.get(0), s))));
            return ret;
        }
        if (stl instanceof TemporalAnd) {
            List<TemporalLogic<I>> subFmls = ((TemporalAnd<I>) stl).getSubFormulas();
            List<IntervalTL<I>> ret = new ArrayList<>();

            ret.addAll(findIntervalSTL(subFmls.get(0), (s) -> frame.apply(new TemporalAnd<>(s, subFmls.get(1)))));
            ret.addAll(findIntervalSTL(subFmls.get(1), (s) -> frame.apply(new TemporalAnd<>(subFmls.get(0), s))));
            return ret;
        }
        if (stl instanceof TemporalGlobally) {
            TemporalLogic<I> subFml = ((TemporalGlobally<I>) stl).getSubFml();
            List<IntervalTL<I>> ret = new ArrayList<>();
            ret.addAll(findIntervalSTL(subFml, (s) -> frame.apply(new TemporalGlobally<>(s))));
            return ret;
        }
        if (stl instanceof TemporalSub) {
            TemporalLogic<I> subFml = ((TemporalSub<I>) stl).getSubFml();
            List<IntervalTL<I>> ret = new ArrayList<>();
            ret.add(new IntervalTL<>((TemporalSub<I>) stl, frame, timeWindow));
            return ret;
        }
        if (stl instanceof TemporalNext) {
            TemporalLogic<I> subFml = ((TemporalNext<I>) stl).getSubFml();
            List<IntervalTL<I>> ret = new ArrayList<>();
            ret.add(new IntervalTL<>(new TemporalSub<>(new TemporalGlobally<>(subFml), 1, 1), frame, timeWindow));
            return ret;
        }
        return new ArrayList<>();
    }

    private TemporalLogic<I> nextStrengthenedSTL(int targetIdx) {
        return this.candidateSTLProperties.get(targetIdx).remove(0);
    }

    private static class IntervalTL<I> {
        public TemporalSub<I> stl;
        public Function<TemporalLogic<I>, TemporalLogic<I>> frame;
        private final int timeWindow;
        private final boolean isSTLEventually;
        private boolean isAssignedCurrent = false;
        private boolean isEventuallyInterval = false;
        private final int defaultFrom, defaultTo;
        private int currentFrom, currentTo;

        public IntervalTL(TemporalSub<I> stl, Function<TemporalLogic<I>, TemporalLogic<I>> frame, int timeWindow) {
            this.stl = stl;
            this.defaultFrom = stl.getFrom();
            this.defaultTo = stl.getTo();
            this.frame = frame;
            this.timeWindow = timeWindow;

            TemporalLogic<I> subFml = this.stl.getSubFml();
            this.isSTLEventually = subFml instanceof TemporalEventually;
        }

        public TemporalLogic<I> getOriginalSTL() {
            return this.frame.apply(stl);
        }

        public TemporalLogic<I> strengthInit() {
            TemporalLogic<I> subFml = this.stl.getSubFml();
            if (subFml instanceof TemporalGlobally) {
                return this.frame.apply(subFml);
            } else if (subFml instanceof TemporalEventually) {
                TemporalLogic<I> subFml2 = ((TemporalEventually<I>) subFml).getSubFml();
                return this.frame.apply(new TemporalGlobally<>(subFml2));
            }
            // TODO: implement Until
            return null;
        }

        /**
         * strengthen an STL formula by changing an interval
         *
         * @return a strengthened STL formula
         */
        public TemporalLogic<I> nextStrengthenedSTL() {
            if (!isAssignedCurrent) {
                isAssignedCurrent = true;
                this.currentFrom = 0;
                this.currentTo = this.timeWindow / 2;
                TemporalOp<I> subFml = this.stl.getSubFml();
                if (subFml instanceof TemporalGlobally) {
                    this.currentFrom = this.defaultFrom * 3 / 4;
                    this.currentTo = this.defaultTo + ((this.timeWindow - this.defaultTo) / 2);
                    return this.frame.apply(new TemporalSub<>(subFml, currentFrom, currentTo));
                } else if (subFml instanceof TemporalEventually) {
                    this.currentFrom = this.defaultFrom / 2;
                    this.currentTo = this.defaultFrom + ((this.timeWindow - this.defaultFrom) / 2);
                    TemporalLogic<I> subFml2 = ((TemporalEventually<I>) subFml).getSubFml();
                    return this.frame.apply(new TemporalSub<>(new TemporalGlobally<>(subFml2), currentFrom, currentTo));
                }
                return null;
            }
            if (isSTLEventually && isEventuallyInterval) {
                // when changing the interval of Eventually operator
                if (this.currentFrom > this.defaultFrom && (this.currentFrom - this.defaultFrom) / 2 > 0) {
                    // if 'from' number of the interval is able to change
                    this.currentFrom = this.defaultFrom + ((this.currentFrom - this.defaultFrom) / 2);
                } else {
                    // now change 'to' number of the interval
                    if (this.currentTo >= this.defaultTo || ((this.defaultTo - this.currentTo) / 2) == 0) {
                        // end
                        return null;
                    }
                    this.currentTo = this.defaultTo - ((this.defaultTo - this.currentTo) / 2);
                }
                TemporalOp<I> subFml = this.stl.getSubFml();
                if (subFml instanceof TemporalEventually) {
                    return this.frame.apply(new TemporalSub<>(subFml, currentFrom, currentTo));
                }
            } else {
                // when changing the interval of Globally operator
                if (this.currentFrom < this.defaultFrom && (this.defaultFrom - this.currentFrom) / 2 > 0) {
                    // if 'from' number of the interval is able to change
                    this.currentFrom = this.currentFrom + ((this.defaultFrom - this.currentFrom) / 2);
                } else {
                    // now change 'to' number of the interval
                    if (isSTLEventually) {
                        // if the most outer operator of target STL formula is Eventually
                        if (this.currentTo <= this.defaultFrom + 1) {
                            // change Eventually operator to Globally operator
                            this.isEventuallyInterval = true;
                            this.currentFrom = this.defaultFrom;
                            this.currentTo = this.defaultFrom;
                            TemporalEventually<I> subFml = (TemporalEventually<I>) this.stl.getSubFml();
                            return this.frame.apply(new TemporalSub<>(subFml, defaultFrom, defaultFrom));
                        }
                        this.currentTo = this.defaultFrom + ((this.currentTo - this.defaultFrom) / 2);
                    } else {
                        // if the most outer operator of target STL formula is Globally
                        if (this.currentTo <= this.defaultTo || ((this.currentTo - this.defaultTo) / 2) == 0) {
                            // end
                            return null;
                        }
                        // decrease to half
                        this.currentTo = this.defaultTo + ((this.currentTo - this.defaultTo) / 2);
                    }
                }

                TemporalOp<I> subFml = this.stl.getSubFml();
                if (subFml instanceof TemporalGlobally) {
                    return this.frame.apply(new TemporalSub<>(subFml, currentFrom, currentTo));
                } else if (subFml instanceof TemporalEventually) {
                    TemporalLogic<I> subFml2 = ((TemporalEventually<I>) subFml).getSubFml();
                    return this.frame.apply(new TemporalSub<>(new TemporalGlobally<>(subFml2), currentFrom, currentTo));
                }
            }
            return null;
        }
    }

    @Override
    public boolean allDisproved() {
        return this.falsifiedSTLProperties.containsAll(this.initialSTLs);
    }

    /***
     * Remove all the non-initial STL formulas
     */
    @Override
    public void reset() {
        List<Integer> nonInitialIndices = new ArrayList<>();
        for (int i = 0; i < size(); i++) {
            TemporalLogic<I> stl = this.getSTLProperties().get(i);
            if (!initialSTLs.contains(stl)) {
                nonInitialIndices.add(i);
            }
        }
        this.removeSTLProperties(nonInitialIndices);
    }
}

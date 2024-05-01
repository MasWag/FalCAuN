package net.maswag;

import lombok.extern.slf4j.Slf4j;

/**
 * The RoSI class representing a robust satisfaction interval (RoSI).
 * <p>A RoSI is a range of possible robustness values after concatenating a suffix.</p>
 *
 * Reference: Deshmukh, Jyotirmoy V., et al. "Robust online monitoring of signal temporal logic." Formal Methods in System Design 51 (2017): 5-30.
 */
@Slf4j
public class RoSI {
    Double lowerBound;
    Double upperBound;

    /**
     * Construct a RoSI with a range of values.
     */
    RoSI(double lowerBound, double upperBound) {
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
    }

    /**
     * Construct a RoSI with a single value, i.e., the lower bound and the upper bound are the same.
     */
    RoSI(double value) {
        this.lowerBound = value;
        this.upperBound = value;
    }

    /**
     * The elementwise max of two RoSIs.
     */
    RoSI max(RoSI element) {
        return new RoSI(
                Double.max(lowerBound, element.lowerBound),
                Double.max(upperBound, element.upperBound));
    }

    /**
     * Destructive max, i.e., assign the elementwise max of two RoSIs to this RoSI.
     * @param element the RoSI to compare with
     * @return this RoSI
     */
    RoSI assignMax(RoSI element) {
        lowerBound = Double.max(lowerBound, element.lowerBound);
        upperBound = Double.max(upperBound, element.upperBound);
        return this;
    }

    /**
     * The elementwise min of two RoSIs.
     */
    RoSI min(RoSI element) {
        return new RoSI(
                Double.min(lowerBound, element.lowerBound),
                Double.min(upperBound, element.upperBound));
    }

    /**
     * Destructive min, i.e., assign the elementwise min of two RoSIs to this RoSI.
     * @param element the RoSI to compare with
     * @return this RoSI
     */
    RoSI assignMin(RoSI element) {
        lowerBound = Double.min(lowerBound, element.lowerBound);
        upperBound = Double.min(upperBound, element.upperBound);
        return this;
    }

    /**
     * Negate the RoSI.
     * @return the negated RoSI
     */
    RoSI negate() {
        return new RoSI(-upperBound, -lowerBound);
    }

    /**
     * Destructive negate, i.e., assign the negated RoSI to this RoSI.
     * @return this RoSI
     */
    RoSI assignNegate() {
        double tmp = lowerBound;
        lowerBound = -upperBound;
        upperBound = -tmp;
        return this;
    }

    /**
     * Compute the robustness value of the RoSI as a single value.
     */
    Double getRobustness() {
        if (Double.isFinite(upperBound)) {
            return upperBound;
        } else if (Double.isFinite(lowerBound)) {
            return lowerBound;
        } else {
            return upperBound;
        }
    }
}

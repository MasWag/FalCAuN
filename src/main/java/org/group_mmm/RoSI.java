package org.group_mmm;

import lombok.extern.slf4j.Slf4j;

@Slf4j
class RoSI {
    Double lowerBound;
    Double upperBound;

    RoSI(double lowerBound, double upperBound) {
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
    }

    RoSI(double value) {
        this.lowerBound = value;
        this.upperBound = value;
    }

    RoSI max(RoSI element) {
        return new RoSI(
                Double.max(lowerBound, element.lowerBound),
                Double.max(upperBound, element.upperBound));
    }

    RoSI assignMax(RoSI element) {
        lowerBound = Double.max(lowerBound, element.lowerBound);
        upperBound = Double.max(upperBound, element.upperBound);
        return this;
    }

    RoSI min(RoSI element) {
        return new RoSI(
                Double.min(lowerBound, element.lowerBound),
                Double.min(upperBound, element.upperBound));
    }

    /**
     * Destructive min
     */
    RoSI assignMin(RoSI element) {
        lowerBound = Double.min(lowerBound, element.lowerBound);
        upperBound = Double.min(upperBound, element.upperBound);
        return this;
    }

    RoSI negate() {
        return new RoSI(-upperBound, -lowerBound);
    }

    RoSI assignNegate() {
        double tmp = lowerBound;
        lowerBound = -upperBound;
        upperBound = -tmp;
        return this;
    }

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

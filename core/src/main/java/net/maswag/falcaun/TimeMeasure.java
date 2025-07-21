package net.maswag.falcaun;

/**
 * Time measurement utility for tracking elapsed time in nanoseconds.
 *
 * This class provides methods to start, stop, and reset time measurements,
 * as well as retrieve the accumulated time in seconds or nanoseconds.
 */
public class TimeMeasure {
    private long accumulatedTime = 0;
    private boolean measuring = false;
    private long startTime;

    public void start() {
        if (measuring) {
            throw new RuntimeException("start is called before stop is called");
        }
        startTime = System.nanoTime();
        measuring = true;
    }

    public void stop() {
        if (measuring) {
            long endTime = System.nanoTime();
            accumulatedTime += endTime - startTime;
            measuring = false;
        } else {
            throw new RuntimeException("stop is called before start is called");
        }
    }

    public void reset() {
        startTime = 0;
        accumulatedTime = 0;
        measuring = false;
    }

    public double getSecond() {
        return this.accumulatedTime / 1000000000.0;
    }

    public double getNanosecond() {
        return this.accumulatedTime;
    }
}

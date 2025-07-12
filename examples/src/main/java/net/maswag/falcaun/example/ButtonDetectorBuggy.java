package net.maswag.falcaun.example;

import de.learnlib.exception.SULException;
import de.learnlib.sul.ObservableSUL;
import de.learnlib.sul.SUL;
import lombok.Getter;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

public class ButtonDetectorBuggy
        implements SUL<ButtonDetector.RawInput, ButtonDetector.ButtonEvent>,
        ObservableSUL<ButtonDetector.DetectorState, ButtonDetector.RawInput, ButtonDetector.ButtonEvent>,
        AutoCloseable {

    private static class Detector {
        private int stepIndex;
        private int pressIndex;
        private int lastReleaseIndex;
        private int clickCount;
        private final int stepMillis;

        public Detector(int stepMillis) {
            this.stepMillis = stepMillis;
            reset();
        }

        public void reset() {
            stepIndex = 0;
            pressIndex = -1;
            lastReleaseIndex = -1;
            clickCount = 0;
        }

        public ButtonDetector.ButtonEvent step(ButtonDetector.RawInput input) {
            ButtonDetector.ButtonEvent result = ButtonDetector.ButtonEvent.None;

            switch (input) {
                case Pressed -> {
                    if (pressIndex < 0) {
                        // first press: record when it started
                        pressIndex = stepIndex;
                    } else {
                        // BUG: if held beyond 1000ms, emit LongPress on subsequent Pressed
                        int pressDuration = (stepIndex - pressIndex) * stepMillis;
                        if (pressDuration >= 1000) {
                            result = ButtonDetector.ButtonEvent.LongPress;
                            // keep pressIndex so further Pressed continue to emit
                        }
                    }
                }
                case Released -> {
                    if (pressIndex >= 0) {
                        int pressDuration = (stepIndex - pressIndex) * stepMillis;
                        if (pressDuration >= 1000) {
                            result = ButtonDetector.ButtonEvent.LongPress;
                            clickCount = 0;
                        } else {
                            if (clickCount == 0) {
                                lastReleaseIndex = stepIndex;
                                clickCount = 1;
                            } else {
                                int gap = (stepIndex - lastReleaseIndex) * stepMillis;
                                if (gap <= 400) {
                                    result = ButtonDetector.ButtonEvent.DoubleClick;
                                    clickCount = 0;
                                } else {
                                    result = ButtonDetector.ButtonEvent.SingleClick;
                                    clickCount = 1;
                                    lastReleaseIndex = stepIndex;
                                }
                            }
                        }
                        pressIndex = -1;
                    }
                }
            }

            stepIndex++;
            return result;
        }

        public ButtonDetector.ButtonEvent finalizeClick() {
            if (clickCount == 1) {
                clickCount = 0;
                return ButtonDetector.ButtonEvent.SingleClick;
            }
            return ButtonDetector.ButtonEvent.None;
        }

        public ButtonDetector.DetectorState getState() {
            return new ButtonDetector.DetectorState(stepIndex, pressIndex, lastReleaseIndex, clickCount);
        }
    }

    private final Detector detector;
    @Getter private int counter;
    private ButtonDetector.DetectorState currentState;
    public static final int DEFAULT_STEP_MILLIS = 100;

    public ButtonDetectorBuggy() {
        this(DEFAULT_STEP_MILLIS);
    }

    public ButtonDetectorBuggy(int stepMillis) {
        this.detector = new Detector(stepMillis);
        this.counter = 0;
    }

    @Override
    public boolean canFork() {
        return false;
    }

    @Override
    public void pre() {
        detector.reset();
        currentState = null;
    }

    @Override
    public void post() {
        counter++;
    }

    @Nullable
    @Override
    public ButtonDetector.ButtonEvent step(@Nullable ButtonDetector.RawInput input) throws SULException {
        if (input == null) {
            return null;
        }
        ButtonDetector.ButtonEvent event = detector.step(input);
        currentState = detector.getState();
        return event;
    }

    @Nonnull
    @Override
    public ObservableSUL<ButtonDetector.DetectorState, ButtonDetector.RawInput, ButtonDetector.ButtonEvent> fork() {
        throw new UnsupportedOperationException("ButtonDetectorBuggy does not support forking");
    }

    @Override
    public ButtonDetector.DetectorState getState() {
        return (currentState != null)
                ? currentState
                : new ButtonDetector.DetectorState(0, -1, -1, 0);
    }

    public void clear() {
        counter = 0;
    }

    public Word<ButtonDetector.ButtonEvent> execute(Word<ButtonDetector.RawInput> inputSignal) {
        if (inputSignal.isEmpty()) {
            return Word.epsilon();
        }

        pre();
        WordBuilder<ButtonDetector.ButtonEvent> output = new WordBuilder<>();
        for (ButtonDetector.RawInput in : inputSignal) {
            output.add(step(in));
        }
        ButtonDetector.ButtonEvent finalEvent = detector.finalizeClick();
        if (finalEvent != ButtonDetector.ButtonEvent.None) {
            output.add(finalEvent);
        }
        post();

        return output.toWord();
    }

    public ButtonDetector.ButtonEvent finalizeClick() {
        return detector.finalizeClick();
    }

    @Override
    public void close() {
        // nothing to close
    }

    // Demonstration of Option A: repeated Pressed emits LongPress twice in a row
    public static void main(String[] args) throws SULException {
        Detector d = new Detector(100);
        // Hold the button for 1000ms by sending 11 Pressed steps
        for (int i = 0; i < 11; i++) {
            ButtonDetector.ButtonEvent ev = d.step(ButtonDetector.RawInput.Pressed);
            System.out.printf("Step %2d: Pressed → %s%n", i, ev);
        }
    }
}

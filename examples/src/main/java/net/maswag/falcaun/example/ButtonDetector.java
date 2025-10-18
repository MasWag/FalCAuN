package net.maswag.falcaun.example;

import de.learnlib.exception.SULException;
import de.learnlib.sul.ObservableSUL;
import de.learnlib.sul.SUL;
import lombok.Getter;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.*;

public class ButtonDetector implements SUL<ButtonDetector.RawInput, ButtonDetector.ButtonEvent>,
                                      ObservableSUL<ButtonDetector.DetectorState, ButtonDetector.RawInput, ButtonDetector.ButtonEvent>,
                                      AutoCloseable {

    public enum RawInput { Pressed, Released }

    public enum ButtonEvent {
        None, SingleClick, DoubleClick, LongPress
    }

    public static class DetectorState {
        public final int stepIndex;
        public final int pressIndex;
        public final int lastReleaseIndex;
        public final int clickCount;

        public DetectorState(int stepIndex, int pressIndex, int lastReleaseIndex, int clickCount) {
            this.stepIndex = stepIndex;
            this.pressIndex = pressIndex;
            this.lastReleaseIndex = lastReleaseIndex;
            this.clickCount = clickCount;
        }
    }

    public static class Detector {
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

        public ButtonEvent step(RawInput input) {
            ButtonEvent result = ButtonEvent.None;

            switch (input) {
                case Pressed -> {
                    // If not already pressed, record the press index
                    if (pressIndex < 0) {
                        pressIndex = stepIndex;
                    }
                }
                case Released -> {
                    if (pressIndex >= 0) {
                        int pressDuration = (stepIndex - pressIndex) * stepMillis;

                        if (pressDuration >= 1000) {
                            result = ButtonEvent.LongPress;
                            clickCount = 0;
                        } else {
                            if (clickCount == 0) {
                                lastReleaseIndex = stepIndex;
                                clickCount = 1;
                            } else {
                                int gap = (stepIndex - lastReleaseIndex) * stepMillis;
                                if (gap <= 400) {
                                    result = ButtonEvent.DoubleClick;
                                    clickCount = 0;
                                } else {
                                    result = ButtonEvent.SingleClick;
                                    clickCount = 1;
                                    lastReleaseIndex = stepIndex;
                                }
                            }
                        }
                        // Reset press index after processing the release
                        pressIndex = -1;
                    }
                }
            }

            stepIndex++;
            return result;
        }

        // Optionally: finalize any pending click
        public ButtonEvent finalizeClick() {
            if (clickCount == 1) {
                clickCount = 0;
                return ButtonEvent.SingleClick;
            }
            return ButtonEvent.None;
        }

        public DetectorState getState() {
            return new DetectorState(stepIndex, pressIndex, lastReleaseIndex, clickCount);
        }

        public int getStepMillis() {
            return stepMillis;
        }
    }

    private final Detector detector;
    @Getter
    private int counter;
    private DetectorState currentState;
    public static final int DEFAULT_STEP_MILLIS = 100;       // in milliseconds

    /**
     * Constructor with default parameters.
     */
    public ButtonDetector() {
        this(DEFAULT_STEP_MILLIS);
    }

    /**
     * Constructor with custom step milliseconds.
     *
     * @param stepMillis  the time step for the detector (milliseconds)
     */
    public ButtonDetector(int stepMillis) {
        this.detector = new Detector(stepMillis);
        this.counter = 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean canFork() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void pre() {
        detector.reset();
        currentState = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void post() {
        // Increment counter after a complete simulation
        counter++;
    }

    /**
     * Execute the SUL by feeding single step input.
     *
     * @param input the input at one time step (button state)
     * @return the output at one time step (button event)
     */
    @Nullable
    @Override
    public ButtonEvent step(@Nullable RawInput input) throws SULException {
        if (input == null) {
            return null;
        }

        // Process the button input
        ButtonEvent event = detector.step(input);

        // Update current state
        currentState = detector.getState();

        return event;
    }

    /**
     * {@inheritDoc}
     */
    @Nonnull
    @Override
    public ObservableSUL<DetectorState, RawInput, ButtonEvent> fork() throws UnsupportedOperationException {
        throw new UnsupportedOperationException("ButtonDetector does not support forking");
    }

    /**
     * {@inheritDoc}
     * Returns the current state of the button detector.
     *
     * @return the current detector state
     */
    @Override
    public DetectorState getState() {
        // If currentState is null (before first step), return a default state
        if (currentState == null) {
            return new DetectorState(0, -1, -1, 0);
        }
        return currentState;
    }

    /**
     * Reset the counter.
     */
    public void clear() {
        counter = 0;
    }

    /**
     * Execute the SUL by feeding the entire input signal.
     *
     * @param inputSignal the sequence of input signals
     * @return the output signal sequence
     */
    public Word<ButtonEvent> execute(Word<RawInput> inputSignal) {
        if (inputSignal.isEmpty()) {
            return Word.epsilon();
        }

        // Reset the detector before execution
        pre();

        WordBuilder<ButtonEvent> outputBuilder = new WordBuilder<>();

        // Process each input signal
        for (int i = 0; i < inputSignal.size(); i++) {
            RawInput input = inputSignal.getSymbol(i);
            ButtonEvent event = step(input);
            outputBuilder.add(event);
        }

        // Always check for pending clicks at the end
        ButtonEvent finalEvent = detector.finalizeClick();
        if (finalEvent != ButtonEvent.None) {
            outputBuilder.add(finalEvent);
        }

        // Reset the model after execution
        post();

        return outputBuilder.toWord();
    }

    /**
     * Finalize any pending click.
     *
     * @return the button event (SingleClick or None)
     */
    public ButtonEvent finalizeClick() {
        return detector.finalizeClick();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void close() {
        // No resources to close
    }

    // Demonstration
    public static void main(String[] args) {
        Detector detector = new Detector(100); // 100 ms per step

        List<RawInput> inputs = List.of(
            RawInput.Pressed, RawInput.Released, // SingleClick
            RawInput.Pressed, RawInput.Released,
            RawInput.Pressed, RawInput.Released, // DoubleClick
            RawInput.Pressed, RawInput.Pressed, RawInput.Pressed, RawInput.Pressed,
            RawInput.Pressed, RawInput.Pressed, RawInput.Pressed, RawInput.Pressed,
            RawInput.Pressed, RawInput.Released  // LongPress (10+ steps)
        );

        List<ButtonEvent> events = new ArrayList<>();
        for (RawInput input : inputs) {
            events.add(detector.step(input));
        }

        // Finalize any pending single click
        ButtonEvent finalEvent = detector.finalizeClick();
        if (finalEvent != ButtonEvent.None) {
            events.add(finalEvent);
            inputs.add(RawInput.Released); // to keep input-output lengths equal
        }

        for (int i = 0; i < inputs.size(); i++) {
            System.out.printf("%2d: %-8s → %s%n", i, inputs.get(i), events.get(i));
        }
    }
}

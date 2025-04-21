package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.ArrayAlphabet;

/**
 * A mapper for ButtonDetector that converts between String and ButtonDetector types.
 * This makes the ButtonDetector usable with the BlackBoxVerifier.
 */
public class ButtonDetectorMapper implements SUL<String, String> {
    
    private final ButtonDetector buttonDetector;
    
    /**
     * Constructs a new ButtonDetectorMapper with the specified ButtonDetector.
     * 
     * @param buttonDetector The ButtonDetector to map
     */
    public ButtonDetectorMapper(ButtonDetector buttonDetector) {
        this.buttonDetector = buttonDetector;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void pre() {
        buttonDetector.pre();
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void post() {
        buttonDetector.post();
    }
    
    /**
     * Maps abstract input (String) to concrete input (ButtonDetector.RawInput),
     * processes it through the ButtonDetector, and maps the output back to String.
     * 
     * @param input The abstract input as a String ("Pressed" or "Released")
     * @return The abstract output as a String representation of the ButtonEvent
     */
    @Override
    public String step(String input) {
        ButtonDetector.RawInput rawInput = input.equals("Pressed") ? 
            ButtonDetector.RawInput.Pressed : ButtonDetector.RawInput.Released;
        ButtonDetector.ButtonEvent event = buttonDetector.step(rawInput);
        return event.toString();
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
    public SUL<String, String> fork() {
        throw new UnsupportedOperationException("Cannot fork ButtonDetector");
    }
    
    /**
     * Returns the input alphabet for the ButtonDetector.
     *
     * @return An Alphabet containing "Pressed" and "Released" inputs
     */
    public static Alphabet<String> getInputAlphabet() {
        return new ArrayAlphabet<>("Pressed", "Released");
    }
}
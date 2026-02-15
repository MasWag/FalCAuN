package net.maswag.falcaun;

import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.generator.Size;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;
import org.junit.runner.RunWith;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the {@link SignalDeriver} class.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@RunWith(JUnitQuickcheck.class)
public class SignalDeriverTest {
    final private SignalDeriver deriver = new SignalDeriver(SimpleSignalMapper.parse(
            List.of("output(0) - output(1)", "output(0) + output(1)")));

    @Property
    public void testMapInput(@Size(min = 1, max = 10) List<Double> input) {
        // Test mapInput - should pass through the input unchanged
        List<Double> result = deriver.mapInput(input);

        // Verify that the result is the same as the input
        assertSame(input, result);
        assertEquals(input, result);
    }

    @Property
    public void testMapOutput(@Size(min = 1, max = 10) List<Double> input, @Size(min = 2, max = 10) List<Double> output) {
        // Test mapOutput with valid inputs
        IOSignalPiece<List<Double>> ioPiece = new IOSignalPiece<>(input, output);

        IOSignalPiece<List<Double>> result = deriver.mapOutput(ioPiece);
        assertNotNull(result);

        // Verify that the input signal is unchanged
        assertEquals(input, result.getInputSignal());

        // Verify that the output signal has the derived signals appended
        List<Double> derivedOutput = result.getOutputSignal();
        assertEquals(output.size() + 2, derivedOutput.size());
        // Check that the original output signals are preserved
        for (int i = 0; i < output.size(); i++) {
            assertEquals(output.get(i), derivedOutput.get(i));
        }
        // Derived signals
        assertEquals(output.get(0) - output.get(1), derivedOutput.get(output.size()));
        assertEquals(output.get(0) + output.get(1), derivedOutput.get(output.size() + 1));
    }

    @Property
    public void testWithShortOutput(@Size(min = 1, max = 10) List<Double> input, @Size(min = 0, max = 1) List<Double> output) {
        IOSignalPiece<List<Double>> ioPiece = new IOSignalPiece<>(input, output);

        // This should throw an IndexOutOfBoundsException because the signal mapper functions
        // try to access elements in the empty output list
        assertThrows(IndexOutOfBoundsException.class, () -> deriver.mapOutput(ioPiece));
    }

    @Property
    public void testWithEmptySignalMapper(@Size(min = 1, max = 10) List<Double> input, @Size(min = 1, max = 10) List<Double> output) {
        // Create an empty SignalMapper
        SignalDeriver emptyDeriver = new SignalDeriver(new SimpleSignalMapper(Collections.emptyList()));

        // Test mapOutput with empty SignalMapper
        IOSignalPiece<List<Double>> ioPiece = new IOSignalPiece<>(input, output);

        IOSignalPiece<List<Double>> result = emptyDeriver.mapOutput(ioPiece);
        assertNotNull(result);

        // Verify that the output signal is unchanged
        assertEquals(output, result.getOutputSignal());
    }

    @Property
    public void testParseSimple(@Size(min = 1, max = 10) List<Double> input, @Size(min = 2, max = 10) List<Double> output) {
        SignalDeriver parsedDeriver = SignalDeriver.parseSimple(List.of("output(0) + output(1)"));
        IOSignalPiece<List<Double>> result = parsedDeriver.mapOutput(new IOSignalPiece<>(input, output));

        assertEquals(input, result.getInputSignal());
        List<Double> derivedOutput = result.getOutputSignal();
        assertEquals(output.size() + 1, derivedOutput.size());
        for (int i = 0; i < output.size(); i++) {
            assertEquals(output.get(i), derivedOutput.get(i));
        }
        assertEquals(output.get(0) + output.get(1), derivedOutput.get(output.size()));
    }

    @Property
    public void testParseExtended(@Size(min = 1, max = 10) List<Double> input, @Size(min = 1, max = 10) List<Double> output) {
        SignalDeriver parsedDeriver = SignalDeriver.parse(List.of("previous_max_output(0)"));

        List<Double> smallerPrevious = new ArrayList<>(output);
        smallerPrevious.set(0, smallerPrevious.get(0) - 1.0);
        List<List<Double>> previousOutputs = List.of(smallerPrevious, output);

        IOSignalPiece<List<Double>> result = parsedDeriver.mapOutput(
                new ExtendedIOSignalPiece<>(input, output, previousOutputs));

        assertEquals(input, result.getInputSignal());
        List<Double> derivedOutput = result.getOutputSignal();
        assertEquals(output.size() + 1, derivedOutput.size());
        for (int i = 0; i < output.size(); i++) {
            assertEquals(output.get(i), derivedOutput.get(i));
        }
        assertEquals(output.get(0), derivedOutput.get(output.size()));
    }
}

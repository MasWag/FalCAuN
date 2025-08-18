package net.maswag.falcaun;

import com.pholser.junit.quickcheck.From;
import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;
import org.junit.runner.RunWith;

import static org.junit.jupiter.api.Assertions.assertEquals;

@RunWith(JUnitQuickcheck.class)
public class OutputMapperPropertyTest {
    @Property
    public void size(@From(OutputMapperGenerator.class) OutputMapper outputMapper) {
        // Largest and outputMapper should have the same size
        assertEquals(outputMapper.getLargest().size(), outputMapper.getOutputMapper().size());
    }

    @Property
    public void largest(@From(OutputMapperGenerator.class) OutputMapper outputMapper) {
        // Largest should contain the next character of each outputMapper entry (e.g, if outputMapper.get(i) has "a", "b", "c", then largest.get(i) should have "d")
        assertEquals(outputMapper.getLargest().size(), outputMapper.getOutputMapper().size());
        for (int i = 0; i < outputMapper.getOutputMapper().size(); i++) {
            assertEquals(outputMapper.getOutputMapper().get(i).size() + 'a', outputMapper.getLargest().get(i).charValue());
        }
    }
}
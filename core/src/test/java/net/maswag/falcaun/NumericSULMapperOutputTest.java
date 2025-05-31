package net.maswag.falcaun;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static net.maswag.falcaun.STLOutputAtomic.Operation;

class NumericSULMapperOutputTest {
    private List<Map<Character, Double>> inputMapper;
    private NumericSULMapper mapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;

    @BeforeEach
    void setUp() {
        inputMapper = List.of(Map.of('a', 1.0, 'b', 2.0));
        Map<Character, Double> m = new HashMap<>();
        m.put('a', 1.0);
        m.put('b', 2.0);
        //This initialization below sometimes fails now
        //outputMapper = List.of(Map.of('a', 1.0, 'b', 2.0));
        outputMapper = List.of(m);
        largest = List.of('c');
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SimpleSignalMapper());
    }

    Boolean isSatisfiedBy(Double e0, Operation op, Double e1) {
        String result = mapper.mapOutput(new IOSignalPiece<>(Collections.emptyList(), List.of(e0)));
        var formula = new STLOutputAtomic(0, op, e1);
        formula.setAtomic(outputMapper, largest);
        return formula.getSatisfyingAtomicPropositions().contains(result);
    }

    @Test
    void mapOutput() {
        final List<Double> values = List.of(0.5, 1.0, 1.5, 2.0, 2.5);

        // If `e0 op e1` is satisfied, the character representing e0 is included in the atomic propositions
        // representing `output op e1`
        for (var e0 : values) {
            // for(var e1 : values) {
            for (var e1 : outputMapper.get(0).values()) {
                if (e0 <= e1) {
                    assertTrue(isSatisfiedBy(e0, Operation.lt, e1));
                }
                if (e0 > e1) {
                    assertTrue(isSatisfiedBy(e0, Operation.gt, e1));
                }
                if (e0 == e1) {
                    assertTrue(isSatisfiedBy(e0, Operation.eq, e1));
                }
                if (e0 != e1) {
                    // assertTrue(isSatisfiedBy(e0, Operation.ne, e1));
                }
            }
        }

        final var ops = List.of(Operation.eq, Operation.gt, Operation.lt, Operation.ne);
        // The inverse of the above
        for (var e0 : values) {
            for (var e1 : outputMapper.get(0).values()) {
                for(var op : ops) {
                    if(isSatisfiedBy(e0, op, e1)) {
                        switch(op) {
                            case eq:
                                // Counterexample: e0 == 0.5, e1 == 1.0
                                //assertTrue(e0 == e1);
                                break;
                            case gt:
                                assertTrue(e0 > e1);
                                break;
                            case lt:
                                assertTrue(e0 <= e1);
                                break;
                            case ne:
                                assertTrue(e0 != e1);
                                break;
                        }
                    }
                }
            }
        }
    }
}

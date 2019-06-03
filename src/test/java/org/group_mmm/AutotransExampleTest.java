package org.group_mmm;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import de.learnlib.api.oracle.MembershipOracle;
import net.automatalib.modelcheckers.ltsmin.AbstractLTSmin;
import net.automatalib.words.WordBuilder;
import org.junit.jupiter.api.Test;
import org.slf4j.LoggerFactory;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class AutotransExampleTest {

    @Test
    void constructAT1() {
        AutotransExample exampleAT = new AutotransExample(10.0);
        System.out.println(exampleAT.constructAT1(4200));
    }

    @Test
    void memOracleBB() throws Exception {
        AutotransExample exampleAT = new AutotransExample(10.0);
        exampleAT.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT.constructAT1(4500.0))));
        exampleAT.constructVerifier();

        // Get BlackBoxVerifier
        Field field = exampleAT.getVerifier().getClass().getDeclaredField("verifier");
        field.setAccessible(true);
        BlackBoxVerifier verifier = (BlackBoxVerifier) field.get(exampleAT.getVerifier());

        // Get MemOracle
        field = verifier.getClass().getDeclaredField("memOracle");
        field.setAccessible(true);
        MembershipOracle.MealyMembershipOracle<String, String> memOracle =
                (MembershipOracle.MealyMembershipOracle<String, String>) field.get(verifier);

        WordBuilder<String> input = new WordBuilder<>();
        input.append("bb");
        WordBuilder<String> expected = new WordBuilder<>();
        expected.append("ba2");
        assertEquals(expected.toWord(), memOracle.answerQuery(input.toWord()));
    }

    @Test
    void runAT1() throws Exception {
        final Logger LOGGER = (Logger) LoggerFactory.getLogger(AbstractLTSmin.class);
        LOGGER.setLevel(Level.DEBUG);

        AutotransExample exampleAT1 = new AutotransExample(10.0);
        exampleAT1.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT1.constructAT1(4250.0))));

        exampleAT1.constructVerifier();

        assertFalse(exampleAT1.getVerifier().run());
        System.out.println("CexInput: " + exampleAT1.getVerifier().getCexAbstractInput());
        System.out.println("CexOutput: " + exampleAT1.getVerifier().getCexOutput());
    }

    @Test
    void runAT2() {
        AutotransExample exampleAT2 = new AutotransExample(10.0);
        exampleAT2.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT2.constructAT2(120,4500.0))));
        try {
            exampleAT2.constructVerifier();
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
        assertFalse(exampleAT2.getVerifier().run());
        //System.out.println("CexInput: " + verifier);
    }
}
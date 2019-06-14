package org.group_mmm;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class ArgParserTest {
    private boolean quitExpect;
    private ArgParser argParser;
    private List<String> args;
    private boolean verboseExpected;

    @BeforeEach
    void setUp() {
        args = new ArrayList<>();
        args.add("cyveria");
    }

    private void addHelp() {
        args.add("-h");
    }

    private void addVersion() {
        args.add("-V");
    }

    private void addVerbose() {
        args.add("-v");
    }

    private void addSTLString() {
        args.add("-e=[] (signal(0) > 100)");
    }

    private void addSTLFile() {
        args.add("-f=stl.txt");
    }

    private void addInputMapper() {
        args.add("-I=input.mapper.txt");
    }

    private void addOutputMapper() {
        args.add("-O=output.mapper.txt");
    }

    private void addHC() {
        args.add("-E=HC");
    }

    private void addLength() {
        args.add("-l=15");
    }

    private void addStepTime() {
        args.add("-s=2.0");
    }

    private void addRandom() {
        args.add("-E=random");
    }


    private void addWP() {
        args.add("-E=WP");
    }

    private void addDot() {
        args.add("-o=result.dot");
    }

    private void parse() {
        argParser = new ArgParser(args.toArray(new String[0]));
    }

    @Test
    void missingSTL() {
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addWP();
        addVerbose();
        assertThrows(IllegalArgumentException.class, this::parse);
    }

    @Test
    void missingInputMapper() {
        addSTLFile();
        addOutputMapper();
        addWP();
        addLength();
        addStepTime();
        addVerbose();
        assertThrows(IllegalArgumentException.class, this::parse);
    }

    @Test
    void missingOutputMapper() {
        addSTLFile();
        addInputMapper();
        addWP();
        addLength();
        addStepTime();
        addVerbose();
        assertThrows(IllegalArgumentException.class, this::parse);
    }

    @Test
    void missingLength() {
        addInputMapper();
        addOutputMapper();
        addWP();
        addSTLString();
        addStepTime();
        addVerbose();
        assertThrows(IllegalArgumentException.class, this::parse);
    }

    @Test
    void missingStepTime() {
        addSTLFile();
        addOutputMapper();
        addLength();
        addWP();
        addVerbose();
        assertThrows(IllegalArgumentException.class, this::parse);
    }

    @Nested
    class Success {

        @Test
        void help() {
            addHelp();
            parse();
            quitExpect = true;
            verboseExpected = false;
        }

        @Test
        void version() {
            addVersion();
            parse();
            quitExpect = true;
            verboseExpected = false;
        }

        @AfterEach
        void tearDown() {
            assertEquals(quitExpect, argParser.isQuit());
            assertEquals(verboseExpected, argParser.isVerbose());
        }

        @Nested
        class NonQuit {

            @AfterEach
            void tearDown() {
                assertEquals(2.0, argParser.getStepTime());
                assertEquals(15, argParser.getLength());
            }

            @Test
            void stlString() {
                addSTLString();
                addInputMapper();
                addOutputMapper();
                addHC();
                addLength();
                addStepTime();
                parse();
                quitExpect = false;
                verboseExpected = false;
                assertNull(argParser.getDotFile());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.HC, argParser.getEquiv());
                assertEquals("[] (signal(0) > 100)", argParser.getStlFormula());
                assertNull(argParser.getStlFile());
            }

            @Test
            void stlFile() {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addRandom();
                addLength();
                addStepTime();
                addDot();
                parse();
                quitExpect = false;
                verboseExpected = false;
                assertEquals("result.dot", argParser.getDotFile());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.RANDOM, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertNull(argParser.getStlFormula());
            }

            @Test
            void wp() {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addLength();
                addStepTime();
                addWP();
                addVerbose();
                parse();
                quitExpect = false;
                verboseExpected = true;
                assertNull(argParser.getDotFile());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.WP, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertNull(argParser.getStlFormula());
            }
        }
    }
}
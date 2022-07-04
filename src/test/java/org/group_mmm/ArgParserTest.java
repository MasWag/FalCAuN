package org.group_mmm;

import org.apache.commons.cli.MissingOptionException;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class ArgParserTest {
    private boolean quitExpect;
    private ArgParser argParser;
    private List<String> args;
    private boolean verboseExpected;
    private int maxTestExpected;

    @BeforeEach
    void setUp() {
        args = new ArrayList<>();
        args.add("falcaun");
        maxTestExpected = 50000;
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

    private void addSA() {
        args.add("-E=SA");
    }

    private void addSAAlpha() {
        args.add("--sa-alpha=0.2");
    }

    private void addLength() {
        args.add("-l=15");
    }

    private void addTimeout() {
        args.add("-t=10");
    }

    private void addStepTime() {
        args.add("-s=2.0");
    }

    private void addMaxTest() {
        args.add("-M=100");
    }

    private void addInitScript() {
        args.add("--init=initAT");
    }

    private void addParamNames() {
        args.add("--param-names=throttle    brake");
    }

    private void addRandom() {
        args.add("-E=random");
    }

    private void addWP() {
        args.add("-E=WP");
    }

    private void addGA() {
        args.add("-E=ga");
    }

    private void addGACrossoverProb() {
        args.add("--ga-crossover-prob=0.5");
    }

    private void addGAMutationProb() {
        args.add("--ga-mutation-prob=0.05");
    }

    private void addGAPopulationSize() {
        args.add("--population-size=100");
    }

    private void addGABestSolution() {
        args.add("--ga-selection-kind=BestSolution");
    }

    private void addGATournament() {
        args.add("--ga-selection-kind=Tournament");
    }

    private void addGAInvalidSolution() {
        args.add("--ga-selection-kind=Hoge");
    }

    private void addDot() {
        args.add("-o=result.dot");
    }

    private void addWpMaxDepth() {
        args.add("--wp-max-depth=10");
    }

    private void addSimulinkSimulationStep() {
        args.add("--simulink-simulation-step=0.01");
    }
    private void parse() throws MissingOptionException, IOException {
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
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingInputMapper() {
        addSTLFile();
        addOutputMapper();
        addWP();
        addLength();
        addStepTime();
        addVerbose();
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingOutputMapper() {
        addSTLFile();
        addInputMapper();
        addWP();
        addLength();
        addStepTime();
        addVerbose();
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingLength() {
        addInputMapper();
        addOutputMapper();
        addWP();
        addSTLString();
        addStepTime();
        addVerbose();
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingSAAlpha() {
        addInputMapper();
        addOutputMapper();
        addSA();
        addSTLString();
        addStepTime();
        addVerbose();
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingStepTime() {
        addSTLFile();
        addOutputMapper();
        addLength();
        addWP();
        addVerbose();
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingInitScript() {
        addSTLFile();
        addOutputMapper();
        addLength();
        addWP();
        addVerbose();
        addStepTime();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingParamNames() {
        addSTLFile();
        addOutputMapper();
        addLength();
        addWP();
        addVerbose();
        addInitScript();
        addStepTime();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void invalidSolutionKind() {
        addSTLFile();
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addGA();
        addMaxTest();
        addVerbose();
        addParamNames();
        addInitScript();
        addGACrossoverProb();
        addGAMutationProb();
        addGAPopulationSize();
        addGAInvalidSolution();
        assertThrows(IllegalArgumentException.class, this::parse);
    }

    @Test
    void missingSolutionKind() {
        addSTLFile();
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addGA();
        addMaxTest();
        addVerbose();
        addParamNames();
        addInitScript();
        addGACrossoverProb();
        addGAMutationProb();
        addGAPopulationSize();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingPopulationSize() {
        addSTLFile();
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addGA();
        addMaxTest();
        addVerbose();
        addParamNames();
        addInitScript();
        addGACrossoverProb();
        addGAMutationProb();
        addGATournament();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingMutationProb() {
        addSTLFile();
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addGA();
        addMaxTest();
        addVerbose();
        addParamNames();
        addInitScript();
        addGACrossoverProb();
        addGAPopulationSize();
        addGATournament();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingCrossoverProb() {
        addSTLFile();
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addGA();
        addMaxTest();
        addVerbose();
        addParamNames();
        addInitScript();
        addGAMutationProb();
        addGAPopulationSize();
        addGATournament();
        assertThrows(MissingOptionException.class, this::parse);
    }

    @Test
    void missingMaxDepth() {
        addSTLFile();
        addInputMapper();
        addOutputMapper();
        addLength();
        addStepTime();
        addWP();
        addMaxTest();
        addVerbose();
        addParamNames();
        addInitScript();
        assertThrows(MissingOptionException.class, this::parse);

    }

    @Nested
    class Success {

        @Test
        void help() throws MissingOptionException, IOException {
            addHelp();
            parse();
            quitExpect = true;
            verboseExpected = false;
        }

        @Test
        void version() throws MissingOptionException, IOException {
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
                assertEquals(maxTestExpected, argParser.getMaxTest());
            }

            @Test
            void stlString() throws MissingOptionException, IOException {
                addSTLString();
                addInputMapper();
                addOutputMapper();
                addHC();
                addLength();
                addStepTime();
                addParamNames();
                addInitScript();
                parse();
                quitExpect = false;
                verboseExpected = false;
                assertNull(argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.HC, argParser.getEquiv());
                assertEquals("[] (signal(0) > 100)", argParser.getStlFormula());
                assertNull(argParser.getStlFile());
                assertNull(argParser.getTimeout());
                assertEquals(0.0025, argParser.getSimulinkSimulationStep());
            }

            @Test
            void stlFile() throws MissingOptionException, IOException {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addRandom();
                addLength();
                addStepTime();
                addDot();
                addParamNames();
                addInitScript();
                addTimeout();
                parse();
                quitExpect = false;
                verboseExpected = false;
                assertEquals("result.dot", argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.RANDOM, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertNull(argParser.getStlFormula());
                assertEquals(10, (long) argParser.getTimeout());
            }

            @Test
            void wp() throws MissingOptionException, IOException {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addLength();
                addStepTime();
                addWP();
                addMaxTest();
                addVerbose();
                addParamNames();
                addInitScript();
                addWpMaxDepth();
                parse();
                quitExpect = false;
                verboseExpected = true;
                maxTestExpected = 100;
                assertNull(argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.WP, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertNull(argParser.getStlFormula());
            }

            @Test
            void sa() throws MissingOptionException, IOException {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addLength();
                addStepTime();
                addSA();
                addSAAlpha();
                addMaxTest();
                addVerbose();
                addParamNames();
                addInitScript();
                parse();
                quitExpect = false;
                verboseExpected = true;
                maxTestExpected = 100;
                assertNull(argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.SA, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertEquals(0.2, (double) argParser.getAlpha());
                assertNull(argParser.getStlFormula());
            }

            @Test
            void gaBestSolution() throws MissingOptionException, IOException {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addLength();
                addStepTime();
                addGA();
                addMaxTest();
                addVerbose();
                addParamNames();
                addInitScript();
                addGACrossoverProb();
                addGAMutationProb();
                addGAPopulationSize();
                addGABestSolution();
                parse();
                quitExpect = false;
                verboseExpected = true;
                maxTestExpected = 100;
                assertNull(argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.GA, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertEquals(ArgParser.GASelectionKind.BestSolution, argParser.getSelectionKind());
                assertNull(argParser.getStlFormula());
            }

            @Test
            void gaTournament() throws MissingOptionException, IOException {
                addSTLFile();
                addInputMapper();
                addOutputMapper();
                addLength();
                addStepTime();
                addGA();
                addMaxTest();
                addVerbose();
                addParamNames();
                addInitScript();
                addGACrossoverProb();
                addGAMutationProb();
                addGAPopulationSize();
                addGATournament();
                parse();
                quitExpect = false;
                verboseExpected = true;
                maxTestExpected = 100;
                assertNull(argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.GA, argParser.getEquiv());
                assertEquals("stl.txt", argParser.getStlFile());
                assertEquals(ArgParser.GASelectionKind.Tournament, argParser.getSelectionKind());
                assertNull(argParser.getStlFormula());
            }

            @Test
            void simulinkSimulationStep() throws MissingOptionException, IOException {
                addSTLString();
                addInputMapper();
                addOutputMapper();
                addHC();
                addLength();
                addStepTime();
                addParamNames();
                addInitScript();
                addSimulinkSimulationStep();
                parse();
                quitExpect = false;
                verboseExpected = false;
                assertNull(argParser.getDotFile());
                assertEquals("initAT", argParser.getInitScript());
                assertEquals(Arrays.asList("throttle", "brake"), argParser.getParamNames());
                assertEquals("input.mapper.txt", argParser.getInputMapperFile());
                assertEquals("output.mapper.txt", argParser.getOutputMapperFile());
                assertEquals(ArgParser.EquivType.HC, argParser.getEquiv());
                assertEquals("[] (signal(0) > 100)", argParser.getStlFormula());
                assertNull(argParser.getStlFile());
                assertNull(argParser.getTimeout());
                assertEquals(0.01, argParser.getSimulinkSimulationStep());
            }
        }
    }
}

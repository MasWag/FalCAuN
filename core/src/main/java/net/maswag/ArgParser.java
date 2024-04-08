package net.maswag;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin;
import net.automatalib.modelchecker.ltsmin.LTSminUtil;
import org.apache.commons.cli.*;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;

@Slf4j
public class ArgParser {
    private final Options options = new Options();
    private final HelpFormatter help = new HelpFormatter();
    @Getter
    SignalMapper sigMap;
    @Getter
    private GASelectionKind selectionKind = null;
    @Getter
    private boolean quit = false;
    @Getter
    private boolean verbose;
    @Getter
    private String stlFile;
    @Getter
    private String stlFormula;
    @Getter
    private String inputMapperFile;
    @Getter
    private String outputMapperFile;
    @Getter
    private EquivType equiv;
    @Getter
    private String etfFile;
    @Getter
    private String dotFile;
    @Getter
    private double stepTime;
    @Getter
    private int length;
    @Getter
    private String initScript;
    @Getter
    private List<String> paramNames;
    @Getter
    private int maxTest = 50000;
    @Getter
    private Integer populationSize = null;
    @Getter
    private Double alpha = null;
    @Getter
    private Long timeout = null;
    @Getter
    private Double mutationProb = null;
    @Getter
    private Double crossoverProb = null;
    @Getter
    private int maxDepth;
    @Getter
    private boolean adaptiveSTL = true;
    @Getter
    Double simulinkSimulationStep = 0.0025;

    ArgParser(String[] args) throws MissingOptionException, IOException {
        options.addOption("h", "help", false, "Print a help message");
        options.addOption("v", "verbose", false, "Outputs extra information, mainly for debugging");
        options.addOption("V", "version", false, "Print the version");
        options.addOption("t", "timeout", true, "Set timeout [seconds]");
        options.addOption("f", "stl-file", true, "Read STL formulas from file");
        options.addOption("e", "stl", true, "Specify STLFormulas by signal temporal logic");
        options.addOption("I", "input-mapper", true, "Read the input mapper configuration from file");
        options.addOption("O", "output-mapper", true, "Read the output mapper configuration from file");
        options.addOption("S", "signal-mapper", true, "Read the signal mapper from file");
        options.addOption("E", "equiv", true, "Specify the equivalence query algorithm");
        options.addOption("o", "output-dot", true, "Write the learned Mealy machine to file in DOT format");
        options.addOption(null, "ltsmin-verbose", false, "Outputs extra information of LTSMin");
        options.addOption(null, "output-etf", true, "Write the learned Mealy machine to file in ETF format");
        options.addOption("s", "step-time", true, "The step time of the sampling");
        options.addOption("l", "signal-length", true, "The length of the signals used in the equivalence queries");
        options.addOption("i", "init", true, "The initial script of MATLAB");
        options.addOption("p", "param-names", true, "The parameter names of the Simulink model");
        options.addOption("M", "max-test", true, "The maximum test size");
        options.addOption(null, "population-size", true, "The population size for GA");
        options.addOption(null, "sa-alpha", true, "The alpha parameter for simulated annealing (should be [0,1])");
        options.addOption(null, "ga-crossover-prob", true, "The crossover probability for genetic algorithm (should be [0,1])");
        options.addOption(null, "ga-mutation-prob", true, "The mutation probability for genetic algorithm (should be [0,1])");
        options.addOption(null, "ga-selection-kind", true, "Specify the selection method in GA");
        options.addOption(null, "wp-max-depth", true, "Specify the maximum depth in Wp");
        options.addOption(null, "disable-adaptive-stl", false, "Disable the adaptive STL updater");
        options.addOption(null, "simulink-simulation-step", true, "The simulation step of Simulink model. This is 0.0025 by default.");

        DefaultParser parser = new DefaultParser();
        CommandLine cl;

        try {
            cl = parser.parse(options, args);
        } catch (ParseException error) {
            System.out.println("error parsing the argument");
            System.out.println(error.getMessage());
            showHelp();
            quit = true;
            return;
        }
        if (cl.hasOption('h')) {
            showHelp();
            quit = true;
            return;
        }
        if (cl.hasOption('V')) {
            showVersion();
            quit = true;
            return;
        }
        verbose = cl.hasOption('v');
        if (verbose) {
            System.setProperty("org.slf4j.simpleLogger.defaultLogLevel", "DEBUG");
        } else {
            System.setProperty("org.slf4j.simpleLogger.defaultLogLevel", "INFO");
        }
        if (cl.hasOption("ltsmin-verbose")) {
            Logger LTSMinLOGGER = (Logger) LoggerFactory.getLogger(AbstractLTSmin.class.toString());
            LTSMinLOGGER.setLevel(Level.DEBUG);
            LTSminUtil.setVerbose(true);
        } else {
            LTSminUtil.setVerbose(false);
        }

        if (cl.hasOption('t')) {
            timeout = Long.parseLong(cl.getOptionValue('t'));
        }

        if (cl.hasOption('f')) {
            stlFile = cl.getOptionValue('f');
        } else if (cl.hasOption('e')) {
            stlFormula = cl.getOptionValue('e');
        } else {
            throw new MissingOptionException("either stl-file or stl must give given!!");
        }

        if (cl.hasOption('I')) {
            inputMapperFile = cl.getOptionValue('I');
        } else {
            throw new MissingOptionException("input-mapper must be specified");
        }

        if (cl.hasOption('O')) {
            outputMapperFile = cl.getOptionValue('O');
        } else {
            throw new MissingOptionException("output-mapper must be specified");
        }

        if (cl.hasOption('l')) {
            length = Integer.parseInt(cl.getOptionValue('l'));
        } else {
            throw new MissingOptionException("signal-length must be specified");
        }

        if (cl.hasOption('s')) {
            stepTime = Double.parseDouble(cl.getOptionValue('s'));
        } else {
            throw new MissingOptionException("step-time must be specified");
        }

        if (cl.hasOption('i')) {
            initScript = cl.getOptionValue('i');
        } else {
            throw new MissingOptionException("init must be specified");
        }

        if (cl.hasOption('p')) {
            paramNames = Arrays.asList(cl.getOptionValue('p').split("\\s+"));
        } else {
            throw new MissingOptionException("param-names must be specified");
        }

        if (cl.hasOption('M')) {
            maxTest = Integer.parseInt(cl.getOptionValue('M'));
        } else {
            log.debug("We use the default value {} for maxTest", maxTest);
        }

        if (cl.hasOption('E')) {
            switch (cl.getOptionValue('E').toLowerCase()) {
                case "hc":
                    equiv = EquivType.HC;
                    break;
                case "random":
                    equiv = EquivType.RANDOM;
                    break;
                case "pure_random":
                    equiv = EquivType.PURE_RANDOM;
                    break;
                case "wp":
                    equiv = EquivType.WP;
                    if (cl.hasOption("wp-max-depth")) {
                        maxDepth = Integer.parseInt(cl.getOptionValue("wp-max-depth"));
                    } else {
                        throw new MissingOptionException("wp-max-depth must be specified for Wp");
                    }
                    break;
                case "sa":
                    equiv = EquivType.SA;
                    if (cl.hasOption("sa-alpha")) {
                        alpha = Double.parseDouble(cl.getOptionValue("sa-alpha"));
                    } else {
                        throw new MissingOptionException("sa-alpha must be specified for SA");
                    }
                    break;
                case "ga":
                    equiv = EquivType.GA;
                    if (cl.hasOption("ga-crossover-prob")) {
                        crossoverProb = Double.parseDouble(cl.getOptionValue("ga-crossover-prob"));
                    } else {
                        throw new MissingOptionException("ga-crossover-prob must be specified for GA");
                    }
                    if (cl.hasOption("ga-mutation-prob")) {
                        mutationProb = Double.parseDouble(cl.getOptionValue("ga-mutation-prob"));
                    } else {
                        throw new MissingOptionException("ga-mutation-prob must be specified for GA");
                    }
                    if (cl.hasOption("population-size")) {
                        populationSize = Integer.parseInt(cl.getOptionValue("population-size"));
                    } else {
                        throw new MissingOptionException("population-size must be specified for GA");
                    }
                    if (cl.hasOption("ga-selection-kind")) {
                        switch (cl.getOptionValue("ga-selection-kind").toLowerCase()) {
                            case "bestsolution":
                                selectionKind = GASelectionKind.BestSolution;
                                break;
                            case "tournament":
                                selectionKind = GASelectionKind.Tournament;
                                break;
                            default:
                                throw new IllegalArgumentException("unknown selection kind: " + cl.getOptionValue("ga-selection-kind"));
                        }
                    } else {
                        throw new MissingOptionException("ga-selection-kind must be specified for GA");
                    }
                    break;
                default:
                    throw new IllegalArgumentException("unknown equiv. algorithm: " + cl.getOptionValue('E'));
            }
        } else {
            throw new MissingOptionException("equiv must be specified");
        }

        dotFile = cl.getOptionValue('o', null);
        etfFile = cl.getOptionValue("output-etf", null);
        if (cl.hasOption("signal-mapper")) {
            sigMap = SignalMapper.parse(cl.getOptionValue("signal-mapper"));
        } else {
            sigMap = new SignalMapper();
        }
        if (cl.hasOption("disable-adaptive-stl")) {
            adaptiveSTL = false;
        }
        if (cl.hasOption("simulink-simulation-step")) {
            simulinkSimulationStep = Double.parseDouble(cl.getOptionValue("simulink-simulation-step"));
        }
    }

    private void showHelp() {
        help.printHelp("falcaun", options);
    }

    private void showVersion() {
        System.out.println(ArgParser.class.getPackage().getImplementationTitle() + " version " + ArgParser.class.getPackage().getImplementationVersion());
    }

    public enum GASelectionKind {
        BestSolution,
        Tournament
    }

    enum EquivType {
        HC,
        RANDOM,
        WP,
        SA,
        GA,
        PURE_RANDOM
    }
}

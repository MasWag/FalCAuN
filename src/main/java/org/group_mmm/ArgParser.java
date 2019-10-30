package org.group_mmm;

import org.apache.commons.cli.*;
import org.slf4j.LoggerFactory;

import java.util.Arrays;
import java.util.List;

class ArgParser {
    private static final org.slf4j.Logger LOGGER = LoggerFactory.getLogger(ArgParser.class);
    private GASelectionKind selectionKind = null;
    private Options options = new Options();
    private HelpFormatter help = new HelpFormatter();
    private boolean quit = false;
    private boolean verbose;
    private String stlFile;
    private String stlFormula;
    private String inputMapperFile;
    private String outputMapperFile;
    private EquivType equiv;

    private String etfFile;

    private String dotFile;
    private double stepTime;
    private int length;
    private String initScript;
    private List<String> paramNames;
    private int maxTest = 50000;
    private Integer populationSize = null;
    private Double alpha = null;
    private Long timeout = null;
    private Double mutationProb = null;
    private Double crossoverProb = null;
    private int maxDepth;

    ArgParser(String[] args) throws MissingOptionException {
        options.addOption("h", "help", false, "Print a help message");
        options.addOption("v", "verbose", false, "Outputs extra information, mainly for debugging");
        options.addOption("V", "version", false, "Print the version");
        options.addOption("t", "timeout", true, "Set timeout [seconds]");
        options.addOption("f", "stl-file", true, "Read a STL formula from file");
        options.addOption("e", "stl", true, "Specify STLFormulas by signal temporal logic");
        options.addOption("I", "input-mapper", true, "Read the input mapper configuration from file");
        options.addOption("O", "output-mapper", true, "Read the output mapper configuration from file");
        options.addOption("E", "equiv", true, "Specify the equivalence query algorithm");
        options.addOption("o", "output-dot", true, "Write the learned Mealy machine to file in DOT format");
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
            LOGGER.debug("We use the default value {} for maxTest", maxTest);
        }

        if (cl.hasOption('E')) {
            switch (cl.getOptionValue('E').toLowerCase()) {
                case "hc":
                    equiv = EquivType.HC;
                    break;
                case "random":
                    equiv = EquivType.RANDOM;
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

        if (cl.hasOption('o')) {
            dotFile = cl.getOptionValue('o');
        } else {
            dotFile = null;
        }
        if (cl.hasOption("output-etf")) {
            etfFile = cl.getOptionValue("output-etf");
        } else {
            etfFile = null;
        }
    }

    GASelectionKind getSelectionKind() {
        return selectionKind;
    }

    int getMaxDepth() {
        return maxDepth;
    }

    int getPopulationSize() {
        return populationSize;
    }

    String getEtfFile() {
        return etfFile;
    }

    Long getTimeout() {
        return timeout;
    }

    double getAlpha() {
        return alpha;
    }

    double getMutationProb() {
        return mutationProb;
    }

    double getCrossoverProb() {
        return crossoverProb;
    }

    int getMaxTest() {
        return maxTest;
    }

    String getInitScript() {
        return initScript;
    }

    List<String> getParamNames() {
        return paramNames;
    }

    double getStepTime() {
        return stepTime;
    }

    int getLength() {
        return length;
    }

    boolean isQuit() {
        return quit;
    }

    private void showHelp() {
        help.printHelp("falcaun", options);
    }

    boolean isVerbose() {
        return verbose;
    }

    String getStlFile() {
        return stlFile;
    }

    String getStlFormula() {
        return stlFormula;
    }

    String getInputMapperFile() {
        return inputMapperFile;
    }

    String getOutputMapperFile() {
        return outputMapperFile;
    }

    EquivType getEquiv() {
        return equiv;
    }

    String getDotFile() {
        return dotFile;
    }

    private void showVersion() {
        System.out.println(ArgParser.class.getPackage().getImplementationTitle() + " version " + ArgParser.class.getPackage().getImplementationVersion());
    }

    enum GASelectionKind {
        BestSolution,
        Tournament
    }

    enum EquivType {
        HC,
        RANDOM,
        WP,
        SA,
        GA
    }
}

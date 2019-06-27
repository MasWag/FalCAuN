package org.group_mmm;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import net.automatalib.modelcheckers.ltsmin.AbstractLTSmin;
import net.automatalib.modelcheckers.ltsmin.LTSminVersion;
import org.apache.commons.cli.*;
import org.slf4j.LoggerFactory;

import java.util.Arrays;
import java.util.List;

class ArgParser {
    private static final org.slf4j.Logger LOGGER = LoggerFactory.getLogger(ArgParser.class);

    private Options options = new Options();
    private HelpFormatter help = new HelpFormatter();
    private boolean quit = false;
    private boolean verbose;
    private String stlFile;
    private String stlFormula;
    private String inputMapperFile;
    private String outputMapperFile;
    private EquivType equiv;
    private String dotFile;
    private double stepTime;
    private int length;
    private String initScript;
    private List<String> paramNames;
    private int maxTest = 50000;
    private String etfFile = "/tmp/out.etf";
    private double alpha;

    ArgParser(String[] args) throws MissingOptionException {
        options.addOption("h", "help", false, "Print a help message");
        options.addOption("v", "verbose", false, "Outputs extra information, mainly for debugging");
        options.addOption("V", "version", false, "Print the version");
        options.addOption("f", "stl-file", true, "Read a STL formula from file");
        options.addOption("e", "stl", true, "Specify STLFormulas by signal temporal logic");
        options.addOption("I", "input-mapper", true, "Read the input mapper configuration from file");
        options.addOption("O", "output-mapper", true, "Read the output mapper configuration from file");
        options.addOption("E", "equiv", true, "Specify the equivalence query algorithm");
        options.addOption("o", "output", true, "Write the learned Mealy machine to file in DOT format");
        options.addOption("s", "step-time", true, "The step time of the sampling");
        options.addOption("l", "signal-length", true, "The length of the signals used in the equivalence queries");
        options.addOption("i", "init", true, "The initial script of MATLAB");
        options.addOption("p", "param-names", true, "The parameter names of the Simulink model");
        options.addOption("M", "max-test", true, "The maximum test size");
        options.addOption(null, "sa-alpha", true, "The alpha parameter for simulated annealing (should be [0,1])");


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
            Logger LTSminVersionLogger = (Logger) LoggerFactory.getLogger(LTSminVersion.class);
            LTSminVersionLogger.setLevel(Level.INFO);
            Logger AbstractLTSminLogger = (Logger) LoggerFactory.getLogger(AbstractLTSmin.class);
            AbstractLTSminLogger.setLevel(Level.INFO);
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
                    break;
                case "sa":
                    equiv = EquivType.SA;
                    if (cl.hasOption("sa-alpha")) {
                        alpha = Double.parseDouble(cl.getOptionValue("sa-alpha"));
                    } else {
                        throw new MissingOptionException("sa-alpha must be specified for SA");
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
    }

    double getAlpha() {
        return alpha;
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
        help.printHelp("cyveria", options);
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

    enum EquivType {
        HC,
        RANDOM,
        WP,
        SA
    }
}

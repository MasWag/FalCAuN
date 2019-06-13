package org.group_mmm;

import org.apache.commons.cli.*;

class ArgParser {
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

    ArgParser(String[] args) {
        options.addOption("h", "help", false, "Print a help message");
        options.addOption("v", "verbose", false, "Outputs extra information, mainly for debugging");
        options.addOption("V", "version", false, "Print the version");
        options.addOption("f", "stl-file", true, "Read a STL formula from file");
        options.addOption("e", "stl", true, "Specify STLFormulas by signal temporal logic");
        options.addOption("I", "input-mapper", true, "Read the input mapper configuration from file");
        options.addOption("O", "output-mapper", true, "Read the output mapper configuration from file");
        options.addOption("E", "equiv", true, "Specify the equivalence query algorithm");
        options.addOption("o", "output", true, "Write the learned Mealy machine to file in DOT format");
        DefaultParser parser = new DefaultParser();
        CommandLine cl;

        try {
            cl = parser.parse(options, args);
        } catch (ParseException ignore) {
            System.out.println("error parsing the argument");
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

        if (cl.hasOption('f')) {
            stlFile = cl.getOptionValue('f');
        } else if (cl.hasOption('e')) {
            stlFormula = cl.getOptionValue('e');
        } else {
            throw new IllegalArgumentException("either stl-file or stl must give given!!");
        }

        if (cl.hasOption('I')) {
            inputMapperFile = cl.getOptionValue('I');
        } else {
            throw new IllegalArgumentException("input-mapper must be specified");
        }

        if (cl.hasOption('O')) {
            outputMapperFile = cl.getOptionValue('O');
        } else {
            throw new IllegalArgumentException("output-mapper must be specified");
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
                default:
                    throw new IllegalArgumentException("unknown equiv. algorithm: " + cl.getOptionValue('E'));
            }
        } else {
            throw new IllegalArgumentException("equiv must be specified");
        }

        if (cl.hasOption('o')) {
            dotFile = cl.getOptionValue('o');
        } else {
            dotFile = null;
        }
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
        System.out.println(Main.class.getPackage().getImplementationTitle() + " version " + Main.class.getPackage().getImplementationVersion());
    }

    enum EquivType {
        HC,
        RANDOM,
        WP
    }
}

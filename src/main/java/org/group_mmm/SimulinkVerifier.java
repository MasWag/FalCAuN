package org.group_mmm;

import de.learnlib.api.SUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.mapper.MappedSUL;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Verifier of a Simulink model
 *
 * @author Masaki Waga <masaki@gmail.com>
 */
class SimulinkVerifier {
    protected SUL<ArrayList<Double>, ArrayList<Double>> simulink;
    private Alphabet<String> abstractInputAlphabet;
    private Alphabet<ArrayList<Double>> concreteInputAlphabet;
    private SimulinkSULMapper mapper;
    private MappedSUL<String, String, ArrayList<Double>, ArrayList<Double>> mappedSimulink;
    private BlackBoxVerifier verifier;

    /**
     * @param initScript The MATLAB script called at first. You have to define mdl in the script.
     * @param paramName  The list of input parameters.
     * @param signalStep The signal step in the simulatin
     * @param properties The LTL properties to be verified
     * @param mapper     The I/O mapepr between abstract/concrete Simulink models.
     * @throws Exception It can be thrown from the constrcutor of SimulinkSUL.
     */
    SimulinkVerifier(String initScript, ArrayList<String> paramName, double signalStep, List<String> properties, SimulinkSULMapper mapper) throws Exception {
        this.mapper = mapper;
        this.simulink = new SimulinkSUL(initScript, paramName, signalStep);
        this.concreteInputAlphabet = mapper.constructConcreteAlphabet();
        this.abstractInputAlphabet = mapper.constructAbstractAlphabet();

        this.simulink = SULCache.createTreeCache(this.concreteInputAlphabet, this.simulink);

        this.mappedSimulink = new MappedSUL<>(mapper, simulink);
        verifier = new BlackBoxVerifier(mappedSimulink, properties, abstractInputAlphabet);
    }

    public String getCexProperty() {
        return verifier.getCexProperty();
    }

    Word<String> getCexAbstractInput() {
        return verifier.getCexInput();
    }

    public Word<ArrayList<Double>> getCexConcreteInput() {
        return Word.fromList(getCexAbstractInput().stream().map(s -> mapper.mapInput(s)).collect(Collectors.toList()));
    }


    Word<String> getCexOutput() {
        return verifier.getCexOutput();
    }

    /**
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    boolean run() {
        return verifier.run();
    }

    /**
     * Wirte the DOT of the found counter example.
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    void writeDOT(Appendable a) throws IOException {
        verifier.writeDOT(a);
    }

    /**
     * Visualize the found counter example.
     */
    void visualize() {
        verifier.visualize();
    }
}

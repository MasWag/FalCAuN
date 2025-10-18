package net.maswag.falcaun;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;

import de.learnlib.sul.SULMapper;
import lombok.Getter;
import net.automatalib.alphabet.Alphabet;
import net.maswag.falcaun.parser.TemporalLogic;
import owl.automaton.Automaton;
import owl.ltl.LabelledFormula;
import owl.ltl.parser.LtlParser;
import owl.translations.ltl2dela.NormalformDELAConstruction;

/**
 * Output Mapper for Mealy machine based on Specification-Guided Abstraction.
 *
 * @author Tsubasa Matsumoto {@literal <tsubari96061@gmail.com>}
 */
public class SGAMapper implements SULMapper<String, String, String, String> {
    @Getter
    private final Map<String, String> outputMapper;
    private List<Automaton<NormalformDELAConstruction.State, ?>> automata;

    public SGAMapper(List<TemporalLogic.LTLFormula> formulaList, Alphabet<String> sigma, Alphabet<String> gamma, boolean partial) {
        createDELAs(formulaList, sigma, gamma, partial);
        this.outputMapper = createOutputMapper(sigma, gamma);
    }

    @Override
    public String mapInput(String abstractInput) {
        return abstractInput;
    }

    @Override
    public String mapOutput(String concreteOutput) {
        return outputMapper.get(concreteOutput);
    }


    private Map<String, String> createOutputMapper(Alphabet<String> sigma, Alphabet<String> gamma) {
        Map<String, String> mapper = new HashMap<>();

        List<String> inputs = new ArrayList<>();
        inputs.addAll(sigma);
        List<String> outputs = new ArrayList<>();
        outputs.addAll(gamma);
        final boolean hasInputs = !inputs.isEmpty();
        for (int i = 0; i < outputs.size(); i++) {
            String o1 = outputs.get(i);
            for (int j = 0; j < i; j++) {
                String o2 = outputs.get(j);
                boolean equal = true;  // check if o1 is equivalent to o2
                int iterationCount = hasInputs ? inputs.size() : 1;
                for (int k = 0; k < iterationCount; k++) {
                    BitSet bitSet1 = new BitSet(outputs.size() + inputs.size());
                    bitSet1.set(i);
                    if (hasInputs) {
                        bitSet1.set(outputs.size() + k);
                    }
                    BitSet bitSet2 = new BitSet(outputs.size() + inputs.size());
                    bitSet2.set(j);
                    if (hasInputs) {
                        bitSet2.set(outputs.size() + k);
                    }
                    for (Automaton<NormalformDELAConstruction.State, ?> automaton : automata) {
                        for (NormalformDELAConstruction.State state : automaton.states()) { // for each phi in derivatives, check D_{o1}(phi) is equivalent to D_{o2}(phi)
                            Set<NormalformDELAConstruction.State> successors1 = automaton.successors(state, bitSet1);
                            Set<NormalformDELAConstruction.State> successors2 = automaton.successors(state, bitSet2);
                            equal = successors1.equals(successors2);
                            if (!equal) break;
                        }
                        if (!equal) break;
                    }
                    if (!equal) break;
                }
                if (equal) { // if o1 and o2 are equivalent, map o1 to o2
                    mapper.put(o1, o2);
                    System.out.println(o1 + " is mapped to " + o2);
                    break;
                }
            }
            mapper.putIfAbsent(o1, o1);
        }
        return mapper;
    }

    // Create deterministic Emerson-Lei automata for effective construction of mapper
    private void createDELAs(List<TemporalLogic.LTLFormula> formulaList, Alphabet<String> sigma, Alphabet<String> gamma, boolean partial) {
        automata = new ArrayList<>();
        List<String> alphabets = new ArrayList<>();
        alphabets.addAll(gamma);
        alphabets.addAll(sigma);
        String lastAlphabet = alphabets.get(alphabets.size() - 1);
        for (TemporalLogic.LTLFormula formula : formulaList) {
            owl.ltl.Formula owlFormula = LtlParser.parse(formula.toOwlString() + "&& (" + lastAlphabet + "|| !" + lastAlphabet + ")", alphabets).formula();
            LabelledFormula labelledFormula = LabelledFormula.of(owlFormula, alphabets);
            NormalformDELAConstruction delaconst = new NormalformDELAConstruction(OptionalInt.empty());
            Automaton<NormalformDELAConstruction.State, ?> automaton = delaconst.apply(labelledFormula);
            automata.add(automaton);
            if (partial) {
                List<TemporalLogic<String>> conjunctions = formula.toNnf(false).toDisjunctiveForm().getAllConjunctions();
                for (TemporalLogic<String> conjunction : conjunctions) {
                    owl.ltl.Formula partialOwlFormula = LtlParser.parse(conjunction.toOwlString() + "&& (" + lastAlphabet + "|| !" + lastAlphabet + ")", alphabets).formula();
                    LabelledFormula partialLabelledFormula = LabelledFormula.of(partialOwlFormula, alphabets);
                    NormalformDELAConstruction partialDelaConst = new NormalformDELAConstruction(OptionalInt.empty());
                    Automaton<NormalformDELAConstruction.State, ?> partialAutomaton = partialDelaConst.apply(partialLabelledFormula);
                    automata.add(partialAutomaton);
                }
            }

        }
    }
}

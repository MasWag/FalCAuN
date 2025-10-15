package net.maswag.falcaun;


import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;
import java.util.stream.Collectors;

import owl.automaton.Automaton;
import owl.ltl.LabelledFormula;
import owl.ltl.parser.LtlParser;
import owl.translations.ltl2dela.NormalformDELAConstruction;

public class NumericSULMapperWithSGA extends NumericSULMapper {
    private final Map<String, String> postOutputMapper;
    private final List<TemporalLogic.STLCost> formulaList;
    List<String> gamma;
    private List<Automaton<NormalformDELAConstruction.State,?>> automata;

    public NumericSULMapperWithSGA(List<Map<Character, Double>> inputMapper,
                                List<Character> largestOutputs, List<Map<Character, Double>> outputMapper,
                                SignalMapper sigMap, List<TemporalLogic.STLCost> formulaList, boolean partial){
        super(inputMapper, largestOutputs, outputMapper, sigMap);
        this.formulaList = formulaList;
        this.gamma = constructAbstractAPs(signalAdapter.getAbstractOutputs());
        createNBAs(partial);
        this.postOutputMapper = getOutputMapper();
    }

    private Map<String, String> getOutputMapper(){
        Map<String, String> mapper = new HashMap<>();

        for (int i = 0; i < gamma.size(); i++){
            String o1 = gamma.get(i);
            BitSet bitSet1 = new BitSet(gamma.size());
            bitSet1.set(i);
            for (int j = 0; j < i; j++){
                String o2 = gamma.get(j);
                BitSet bitSet2 = new BitSet(gamma.size());
                bitSet2.set(j);
                boolean equal = true;  // check if o1 is equivalent to o2
                for (Automaton<NormalformDELAConstruction.State,?> automaton: automata){
                    for (NormalformDELAConstruction.State state : automaton.states()){ // for each phi in derivatives, check D_{o1}(phi) is equivalent to D_{o2}(phi)
                        Set<NormalformDELAConstruction.State> successors1 = automaton.successors(state, bitSet1);
                        Set<NormalformDELAConstruction.State> successors2 = automaton.successors(state, bitSet2);
                        equal = equal && successors1.equals(successors2);
                        if (!equal){ break; }
                    }
                    if (!equal){ break; }
                }
                if(equal){ // if o1 and o2 are equivalent, map o1 to o2 
                    mapper.put(o1, o2);
                    System.out.println(o1 + " is mapped to " + o2);
                    break;
                }
            }
            mapper.putIfAbsent(o1, o1);
        }

        return mapper;
    } 

    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        String mappedOutput = super.mapOutput(concreteIO);
        return postOutputMapper.get(mappedOutput);
    }

    public String mapAbstractOutput(String s) {
        return postOutputMapper.get(s);
    }

    private void createNBAs(boolean partial){
        automata = new ArrayList<>();
        for (TemporalLogic.STLCost formula: formulaList) {
            owl.ltl.Formula owlFormula = LtlParser.parse(formula.toOwlString() + "&& ("+ gamma.get(gamma.size()-1) + "|| !" + gamma.get(gamma.size()-1) + ")", gamma).formula();
            LabelledFormula labelledFormula = LabelledFormula.of(owlFormula, gamma);
            NormalformDELAConstruction delaconst = new NormalformDELAConstruction(OptionalInt.empty());
            Automaton<NormalformDELAConstruction.State,?> automaton = delaconst.apply(labelledFormula);
            automata.add(automaton);
            if (partial) {
                List<TemporalLogic<List<Double>>> conjunctions = formula.toNnf(false).toDisjunctiveForm().getAllConjunctions();
                for (TemporalLogic<List<Double>> conjunction: conjunctions){
                    owl.ltl.Formula partialOwlFormula = LtlParser.parse(conjunction.toOwlString() + "&& ("+ gamma.get(gamma.size()-1) + "|| !" + gamma.get(gamma.size()-1) + ")", gamma).formula();
                    LabelledFormula partialLabelledFormula = LabelledFormula.of(partialOwlFormula, gamma);
                    NormalformDELAConstruction partialDelaConst = new NormalformDELAConstruction(OptionalInt.empty());
                    Automaton<NormalformDELAConstruction.State,?> partialAutomaton = partialDelaConst.apply(partialLabelledFormula);
                    automata.add(partialAutomaton);
                    // System.out.println(automaton.atomicPropositions());
                }
            }
            
        }
    }

    private List<String> constructAbstractAPs(List<List<Character>> abstractOutputs){
        List<String> result = new ArrayList<>();
        for (int i = 0; i < abstractOutputs.size(); i++){
            List<Character> abstractOutputi = new ArrayList<>(abstractOutputs.get(i));
            abstractOutputi.add(signalAdapter.getLargestOutputs().get(i));
            List<String> tmpList = new ArrayList<>();
            if (result.isEmpty()){
                tmpList = abstractOutputi.stream().map(c -> String.valueOf(c)).collect(Collectors.toList());
            } else {
                for (String s: result){
                    for ( Character c: abstractOutputi){
                        tmpList.add(s + c);
                    }
                }
            }
            result = tmpList;
        }
        return result;
    }
}
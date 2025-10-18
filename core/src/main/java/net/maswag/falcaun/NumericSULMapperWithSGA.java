package net.maswag.falcaun;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.GrowingMapAlphabet;

/**
 * Output Mapper for NumericSUL baed on Specification-Guided Abstraction.
 *
 * @author Tsubasa Matsumoto {@literal <tsubari96061@gmail.com>}
 */
public class NumericSULMapperWithSGA extends NumericSULMapper {
    private final Map<String, String> postOutputMapper;
    private final SGAMapper sgaMapper;

    public NumericSULMapperWithSGA(List<Map<Character, Double>> inputMapper,
                                List<Character> largestOutputs, List<Map<Character, Double>> outputMapper,
                                SignalMapper sigMap, List<TemporalLogic.STLCost> formulaList, boolean partial){
        super(inputMapper, largestOutputs, outputMapper, sigMap);
        List<String> abstractOutputWords = constructAbstractAPs(signalAdapter.getAbstractOutputs());
        // SGAMapper expects the discretized sigma alphabet and the abstract gamma alphabet
        Alphabet<String> discretizedSigmaAlphabet = signalAdapter.constructAbstractAlphabet();
        Alphabet<String> abstractGammaAlphabet = new GrowingMapAlphabet<>(abstractOutputWords);

        List<TemporalLogic.LTLFormula> ltlFormulas = convertToLtlFormulas(formulaList);
        this.sgaMapper = new SGAMapper(ltlFormulas, discretizedSigmaAlphabet, abstractGammaAlphabet, partial);
        this.postOutputMapper = sgaMapper.getOutputMapper();
    }

    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        String mappedOutput = super.mapOutput(concreteIO);
        return postOutputMapper.get(mappedOutput);
    }

    public String mapAbstractOutput(String s) {
        return postOutputMapper.get(s);
    }

    private List<TemporalLogic.LTLFormula> convertToLtlFormulas(List<TemporalLogic.STLCost> stlFormulas) {
        LTLFactory factory = new LTLFactory();
        return stlFormulas.stream()
                .map(formula -> LTLFormulaHelper.prepareFormula(factory.parse(formula.toLTLString())))
                .collect(Collectors.toList());
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

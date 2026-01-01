package net.maswag.falcaun;

import java.util.List;
import java.util.Map;

import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.GrowingMapAlphabet;
import net.maswag.falcaun.parser.LTLFormulaHelper;
import net.maswag.falcaun.parser.TemporalLogic;

/**
 * Output Mapper for NumericSUL based on Specification-Guided Abstraction.
 *
 * @author Tsubasa Matsumoto {@literal <tsubari96061@gmail.com>}
 */
public class NumericSULMapperWithSGA extends PostComposedSignalDiscretizer {
    private final Map<String, String> postOutputMapper;

    public NumericSULMapperWithSGA(List<Map<Character, Double>> inputMapper,
                                List<Character> largestOutputs, List<Map<Character, Double>> outputMapper,
                                SignalMapper sigMap, List<TemporalLogic.STLCost> formulaList, boolean partial){
        NumericSULMapper baseMapper = new NumericSULMapper(inputMapper, largestOutputs, outputMapper, sigMap);
        List<String> abstractOutputWords = AtomicPropositionUtil.constructAbstractAPs(baseMapper.getAbstractOutputs(), baseMapper.getLargestOutputs());
        // SGAMapper expects the discretized sigma alphabet and the abstract gamma alphabet
        Alphabet<String> discretizedSigmaAlphabet = baseMapper.constructAbstractAlphabet();
        Alphabet<String> abstractGammaAlphabet = new GrowingMapAlphabet<>(abstractOutputWords);

        List<TemporalLogic.LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(formulaList);
        SGAMapper sgaMapper = new SGAMapper(ltlFormulas, discretizedSigmaAlphabet, abstractGammaAlphabet, partial);
        this.postOutputMapper = sgaMapper.getOutputMapper();
        super.setDiscretizer(baseMapper);
        super.setPostMapper(sgaMapper);
    }

    public NumericSULMapperWithSGA(List<Map<Character, Double>> inputMapper,
                                   OutputMapper outputMapper,
                                   SignalMapper sigMap, List<TemporalLogic.STLCost> formulaList, boolean partial) {
        this(inputMapper, outputMapper.getLargest(), outputMapper.getOutputMapper(), sigMap, formulaList, partial);
    }

    @Deprecated
    public NumericSULMapperWithSGA(List<Map<Character, Double>> inputMapper,
                                   OutputMapperReader outputMapperReader,
                                   SignalMapper sigMap, List<TemporalLogic.STLCost> formulaList, boolean partial) {
        this(inputMapper, outputMapperReader.getLargest(), outputMapperReader.getOutputMapper(), sigMap, formulaList, partial);
    }

    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        String mappedOutput = super.mapOutput(concreteIO);
        return postOutputMapper.get(mappedOutput);
    }

    public String mapAbstractOutput(String s) {
        return postOutputMapper.get(s);
    }

    public Map<String, String> getOutputMapper(){
        return this.postOutputMapper;
    }
}

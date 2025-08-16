package net.maswag.falcaun;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import net.automatalib.word.WordBuilder;

import java.util.Collections;
import java.util.List;

public class IOSignalGenerator extends Generator<IOSignal> {
    public IOSignalGenerator() {
        super(IOSignal.class);
    }

    @Override
    public IOSignal<List<Double>> generate(SourceOfRandomness random, GenerationStatus status) {
        IOSignal<List<Double>> signal;

        int size = random.nextInt(32);
        WordBuilder<List<Double>> inputBuilder = new WordBuilder<>();
        WordBuilder<List<Double>> outputBuilder = new WordBuilder<>();

        for (int i = 0; i < size; i++) {
            inputBuilder.append(Collections.singletonList((random.nextDouble() - 0.5) * 2000));
            outputBuilder.append(Collections.singletonList((random.nextDouble() - 0.5) * 2000));
        }
        signal = new IODiscreteSignal<>(inputBuilder.toWord(), outputBuilder.toWord());
        assert signal.size() == size;
        return signal;
    }
}

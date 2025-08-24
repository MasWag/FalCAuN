package net.maswag.falcaun;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import net.automatalib.word.WordBuilder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class OutputMapperGenerator extends Generator<OutputMapper> {
    public OutputMapperGenerator() {
        super(OutputMapper.class);
    }

    @Override
    public OutputMapper generate(SourceOfRandomness random, GenerationStatus status) {
        int dimensions = random.nextInt(10) + 1; // Ensure at least one dimension
        List<List<Double>> data = new ArrayList<>(dimensions);

        for (int i = 0; i < dimensions; i++) {
            int size = random.nextInt(20);
            data.add(new ArrayList<>(size));
            for (int j = 0; j < size; j++) {
                data.get(i).add(random.nextDouble());
            }
            // Sort data.get(i) in ascending order
            Collections.sort(data.get(i));
        }

        assert data.size() == dimensions;
        return new OutputMapper(data);
    }
}

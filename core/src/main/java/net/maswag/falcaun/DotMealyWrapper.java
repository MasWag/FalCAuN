package net.maswag.falcaun;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import lombok.extern.slf4j.Slf4j;
import org.jgrapht.Graph;
import org.jgrapht.graph.DirectedPseudograph;
import org.jgrapht.nio.EdgeProvider;
import org.jgrapht.nio.VertexProvider;
import org.jgrapht.nio.dot.DOTImporter;
import org.jgrapht.util.SupplierUtil;

import lombok.Getter;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.Alphabets;
import net.automatalib.automaton.CompactTransition;
import net.automatalib.automaton.transducer.CompactMealy;
import net.automatalib.util.automaton.builder.AutomatonBuilders;
import net.automatalib.util.automaton.builder.MealyBuilder;


/**
 * 
 * <p>
 * This class provides construction of Mealy machine from DOT file
 *
 * @author Tsubasa Matsumoto {@literal <tsubari96061@gmail.com>}
 */
@Slf4j
public class DotMealyWrapper{
    String fileName;
    Graph<String, LabeledEdge> graph;
    @Getter
    Alphabet<String> sigma;
    @Getter
    Alphabet<String> gamma;

    public DotMealyWrapper(String fileName) {
        this.fileName = fileName;
        graph = new DirectedPseudograph<>(SupplierUtil.createStringSupplier(), SupplierUtil.createSupplier(LabeledEdge.class), false);
        readInputSymbols();
        readOutputSymbols();
        readFromDot();
    }

    public void readInputSymbols() {
        try {
            File file = new File(fileName + ".inputs");
            Reader fileReader;
            BufferedReader buffReader;
            fileReader = new FileReader(file);
            buffReader = new BufferedReader(fileReader);

            List<String> inputSymbols = new ArrayList<>();
            String nextLine = buffReader.readLine();
            while (nextLine != null) {
                nextLine = nextLine.replace("_", "");
                inputSymbols.add(nextLine);
                nextLine = buffReader.readLine();
            }
            buffReader.close();

            sigma = Alphabets.fromList(inputSymbols);
        } catch (IOException e) {
            log.error("Failed to read input symbols from {}", fileName, e);
        }
    }

    public void readOutputSymbols() {
        try {
            File file = new File(fileName + ".outputs");
            Reader fileReader;
            BufferedReader buffReader;
            fileReader = new FileReader(file);
            buffReader = new BufferedReader(fileReader);

            List<String> inputSymbols = new ArrayList<>();
            String nextLine = buffReader.readLine();
            while (nextLine != null) {
                nextLine = nextLine.replace("_", "");
                inputSymbols.add(nextLine);
                nextLine = buffReader.readLine();
            }
            buffReader.close();

            gamma = Alphabets.fromList(inputSymbols);
        } catch (IOException e) {
            log.error("Failed to read output symbols from {}", fileName, e);
        }
    }

    public void readFromDot() {
        File file = new File(fileName + ".dot");
        Reader fileReader;
        try {
            fileReader = new FileReader(file);
        } catch (FileNotFoundException e) {
            log.error("Unable to read DOT file {}", file, e);
            return;
        }
        VertexProvider<String> vertexProvider = (label, attributes) -> label;
        EdgeProvider<String, LabeledEdge> edgeProvider = (from, to, label, attributes) -> {
            LabeledEdge edge = new LabeledEdge();
            edge.setAttrs(attributes);
            return edge;
        };

        DOTImporter<String, LabeledEdge> importer = new DOTImporter<>(vertexProvider, edgeProvider);

        importer.importGraph(graph, fileReader);
    }

    public CompactMealy<String, String> createMealy() {
        return this.createMealy(new HashMap<>());
    }

    public CompactMealy<String, String> createMealy(Map<String, String> mapper) {
        MealyBuilder<Integer,String, CompactTransition<String>, String, CompactMealy<String, String>> mealyBuilder
            = AutomatonBuilders.newMealy(sigma);
        
        Set<LabeledEdge> edgeSet = graph.edgeSet();

        List<LabeledEdge> initialEdge = new ArrayList<>();  // edges without label
        Set<LabeledEdge> otherEdges = new HashSet<>();        // edges with label
        edgeSet.forEach(s -> {
            if (s.isAttrNull()) { initialEdge.add(s); }
            else { otherEdges.add(s); }
        });
        assert (initialEdge.size() == 1);

        Set<String> outputs = new HashSet<>();
        Set<String> inputs = new HashSet<>();
        MealyBuilder<Integer,String, CompactTransition<String>, String, CompactMealy<String, String>>.MealyBuilder__4 mealyBuilderWithEdge = null;
        for (LabeledEdge edge: otherEdges) {
            String attribute = edge.getAttr().orElse("");
            if (attribute.isEmpty()) {
                continue;
            }
            String[] splited = attribute.replace("\"", "").split("/", 2);
            if (splited.length < 2) {
                log.warn("Unexpected edge label format: {}", attribute);
                continue;
            }
            String input = splited[0].replace("_", "");
            inputs.add(input);
            String output = splited[1].replace("_", "");
            if (mapper.containsKey(output)) {
                output = mapper.get(output);
                outputs.add(mapper.get(output));
            } else {
                outputs.add(output);
            }
            if (mealyBuilderWithEdge == null) {
                mealyBuilderWithEdge = mealyBuilder
                .from(edge.getSource())
                .on(input)
                .withOutput(output)
                .to(edge.getTarget());
            } else {
                mealyBuilderWithEdge = mealyBuilderWithEdge
                .from(edge.getSource())
                .on(input)
                .withOutput(output)
                .to(edge.getTarget());
            }
        }

        log.info("input size: {}", inputs.size());
        log.info("output size: {}", outputs.size());

        assert mealyBuilderWithEdge != null;
        return mealyBuilderWithEdge.withInitial(initialEdge.get(0).getTarget()).create();
    }
}

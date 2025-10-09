package net.maswag.falcaun;

import org.jgrapht.*;
import org.jgrapht.graph.*;
import org.jgrapht.nio.*;
import org.jgrapht.nio.dot.*;
import org.jgrapht.traverse.*;
import org.jgrapht.util.SupplierUtil;

import lombok.Getter;
import net.automatalib.alphabet.Alphabets;
import net.automatalib.automaton.CompactTransition;
import net.automatalib.automaton.transducer.CompactMealy;
import net.automatalib.util.automaton.builder.AutomatonBuilders;
import net.automatalib.util.automaton.builder.MealyBuilder;
import net.automatalib.alphabet.Alphabet;

import java.io.*;
import java.net.*;
import java.util.*;

// import org.jgrapht.io.DOTParser;

public class DotMealyWrapper{
    String fileName;
    Graph<String, LabeledEdge> graph;
    @Getter
    Alphabet<String> sigma;
    @Getter
    Alphabet<String> gamma;

    public DotMealyWrapper(String fileName) {
        this.fileName = fileName;
        graph = new DirectedPseudograph<String, LabeledEdge>(SupplierUtil.createStringSupplier(), SupplierUtil.createSupplier(LabeledEdge.class), false);
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
        } catch (FileNotFoundException e) {
            System.out.println(e);
        } catch (IOException e) {
            System.out.println(e);
        }
        
        return;
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
        } catch (FileNotFoundException e) {
            System.out.println(e);
        } catch (IOException e) {
            System.out.println(e);
        }
        return;
    }

    public void readFromDot() {
        File file = new File(fileName + ".dot");
        Reader fileReader;
        try {
            fileReader = new FileReader(file);
        } catch (FileNotFoundException e) {
            System.out.println(e);
            return;
        }
        DOTImporter<String, LabeledEdge> importer = new DOTImporter<>();
        importer.setVertexFactory(label -> label);
        importer.setEdgeWithAttributesFactory(m -> {
            LabeledEdge edge = new LabeledEdge();
            edge.setAttrs(m);
            return edge;
        });

        importer.importGraph(graph, fileReader);

        // Set<LabeledEdge> edges = graph.edgeSet();

        // for (LabeledEdge edge : edges) {
        //     System.out.println(edge);
        // }

        return;
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
        edgeSet.stream().forEach(s -> {
            if (s.isAtrrNull()) { initialEdge.add(s); }
            else { otherEdges.add(s); }
        });
        assert (initialEdge.size() == 1);

        Set<String> outputs = new HashSet<>();
        Set<String> inputs = new HashSet<>();
        MealyBuilder<Integer,String, CompactTransition<String>, String, CompactMealy<String, String>>.MealyBuilder__4 mealyBuilderWithEdge = null;
        for (LabeledEdge edge: otherEdges) {
            String attribute = edge.getAttr();
            //System.out.println(attribute);
            String[] splited = attribute.split("/");
            String input = splited[0].substring(1, splited[0].length()).replace("_", "");
            inputs.add(input);
            String output = splited[1].substring(0, splited[1].length()-1).replace("_", "");
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

        System.out.println("input size:" + inputs.size());
        System.out.println("output size:" + outputs.size());

        // System.out.println("initial: " + initialEdge.get(0).getTarget());
        CompactMealy<String, String> result = mealyBuilderWithEdge.withInitial(initialEdge.get(0).getTarget()).create();

        return result;
    }
}
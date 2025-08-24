package net.maswag.falcaun;

import com.pholser.junit.quickcheck.From;
import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static java.lang.Double.POSITIVE_INFINITY;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the {@link OutputMapper} class.
 * 
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class OutputMapperTest {

    private List<List<Double>> testData;
    private OutputMapper outputMapper;
    
    @TempDir
    Path tempDir;

    @BeforeEach
    void setUp() {
        // Initialize test data
        testData = new ArrayList<>();
        testData.add(Arrays.asList(10.0, 20.0, 30.0));
        testData.add(Arrays.asList(-5.0, 0.0, 5.0));
        
        // Create OutputMapper instance
        outputMapper = new OutputMapper(testData);
    }

    @Test
    void testConstructorWithData() {
        // Test that the constructor properly initializes the object
        assertNotNull(outputMapper);
        assertEquals(testData, outputMapper.getParsedData());
        
        // Test that parse() was called and initialized the outputMapper and largest fields
        assertNotNull(outputMapper.getOutputMapper());
        assertNotNull(outputMapper.getLargest());
        
        // Check the size of outputMapper
        assertEquals(2, outputMapper.getOutputMapper().size());
        
        // Check the size of largest
        assertEquals(2, outputMapper.getLargest().size());
    }

    @Test
    void testParse() {
        // Create a new OutputMapper with different data
        List<List<Double>> newData = new ArrayList<>();
        newData.add(Arrays.asList(1.0, 2.0));
        newData.add(Arrays.asList(3.0, 4.0, 5.0));
        
        OutputMapper newOutputMapper = new OutputMapper(newData);
        
        // Test that parse() was called and initialized the outputMapper and largest fields
        assertNotNull(newOutputMapper.getOutputMapper());
        assertNotNull(newOutputMapper.getLargest());
        
        // Check the size of outputMapper
        assertEquals(2, newOutputMapper.getOutputMapper().size());
        
        // Check the size of largest
        assertEquals(2, newOutputMapper.getLargest().size());
        
        // Check the content of outputMapper
        Map<Character, Double> firstMap = newOutputMapper.getOutputMapper().get(0);
        assertEquals(2, firstMap.size());
        assertEquals(1.0, firstMap.get('a'));
        assertEquals(2.0, firstMap.get('b'));
        
        Map<Character, Double> secondMap = newOutputMapper.getOutputMapper().get(1);
        assertEquals(3, secondMap.size());
        assertEquals(3.0, secondMap.get('a'));
        assertEquals(4.0, secondMap.get('b'));
        assertEquals(5.0, secondMap.get('c'));
        
        // Check the content of largest
        assertEquals('c', newOutputMapper.getLargest().get(0));
        assertEquals('d', newOutputMapper.getLargest().get(1));
    }

    @Test
    void testConstructorWithFilename() throws IOException {
        // Create a temporary file with test data
        Path tempFile = tempDir.resolve("output_mapper_test.tsv");
        List<String> lines = Arrays.asList(
            "10.0\t20.0\t30.0",
            "-5.0\t0.0\t5.0"
        );
        Files.write(tempFile, lines);
        
        // Create OutputMapper instance from file
        OutputMapper fileOutputMapper = new OutputMapper(tempFile.toString());
        
        // Test that the constructor properly initializes the object
        assertNotNull(fileOutputMapper);
        
        // Test that parse() was called and initialized the outputMapper and largest fields
        assertNotNull(fileOutputMapper.getOutputMapper());
        assertNotNull(fileOutputMapper.getLargest());
        
        // Check the size of outputMapper
        assertEquals(2, fileOutputMapper.getOutputMapper().size());
        
        // Check the size of largest
        assertEquals(2, fileOutputMapper.getLargest().size());
        
        // Check the content of outputMapper
        Map<Character, Double> firstMap = fileOutputMapper.getOutputMapper().get(0);
        assertEquals(3, firstMap.size());
        assertEquals(10.0, firstMap.get('a'));
        assertEquals(20.0, firstMap.get('b'));
        assertEquals(30.0, firstMap.get('c'));
        
        Map<Character, Double> secondMap = fileOutputMapper.getOutputMapper().get(1);
        assertEquals(3, secondMap.size());
        assertEquals(-5.0, secondMap.get('a'));
        assertEquals(0.0, secondMap.get('b'));
        assertEquals(5.0, secondMap.get('c'));
    }

    @Test
    void testGetParsedData() {
        // Test the getParsedData method
        List<List<Double>> parsedData = outputMapper.getParsedData();
        assertNotNull(parsedData);
        assertEquals(testData, parsedData);
    }

    @Test
    void testGetOutputMapper() {
        // Test the getOutputMapper method
        List<Map<Character, Double>> mapper = outputMapper.getOutputMapper();
        assertNotNull(mapper);
        assertEquals(2, mapper.size());
        
        // Check the content of the first map
        Map<Character, Double> firstMap = mapper.get(0);
        assertEquals(3, firstMap.size());
        assertEquals(10.0, firstMap.get('a'));
        assertEquals(20.0, firstMap.get('b'));
        assertEquals(30.0, firstMap.get('c'));
        
        // Check the content of the second map
        Map<Character, Double> secondMap = mapper.get(1);
        assertEquals(3, secondMap.size());
        assertEquals(-5.0, secondMap.get('a'));
        assertEquals(0.0, secondMap.get('b'));
        assertEquals(5.0, secondMap.get('c'));
    }

    @Test
    void testGetLargest() {
        List<Character> largest = outputMapper.getLargest();
        assertNotNull(largest);
        assertEquals(2, largest.size());
        assertEquals('d', largest.get(0));
        assertEquals('d', largest.get(1));
    }

    @Test
    void testWithEmptyData() {
        // Test with empty data
        List<List<Double>> emptyData = new ArrayList<>();
        OutputMapper emptyOutputMapper = new OutputMapper(emptyData);
        
        // Test that parse() was called and initialized the outputMapper and largest fields
        assertNotNull(emptyOutputMapper.getOutputMapper());
        assertNotNull(emptyOutputMapper.getLargest());
        
        // Check the size of outputMapper and largest
        assertEquals(0, emptyOutputMapper.getOutputMapper().size());
        assertEquals(0, emptyOutputMapper.getLargest().size());
    }

    @Test
    void testWithNullData() {
        // Test with null data - should throw NullPointerException
        assertThrows(NullPointerException.class, () -> new OutputMapper((List<List<Double>>) null));
    }

    @Test
    void testWithInvalidFilename() {
        // Test with invalid filename - should throw IOException
        assertThrows(IOException.class, () -> new OutputMapper("non_existent_file.tsv"));
    }
}
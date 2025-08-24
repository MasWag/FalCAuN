package net.maswag.falcaun;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the {@link InputMapper} class.
 * 
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
class InputMapperTest {

    private InputMapper inputMapper;
    private InputMapper customCharInputMapper;
    private InputMapper fromMappingsInputMapper;

    @BeforeEach
    void setUp() {
        // Initialize test data
        List<List<Double>> testData = new ArrayList<>();
        testData.add(Arrays.asList(10.0, 20.0, 30.0));
        testData.add(Arrays.asList(-5.0, 0.0, 5.0));
        
        // Initialize custom characters
        char[] customChars = new char[]{'x', 'y'};
        
        // Create InputMapper instances using different factory methods
        inputMapper = InputMapper.make(testData);
        customCharInputMapper = InputMapper.makeWithCustomChars(testData, customChars);
        
        // Create mappings for fromMappings test
        List<Map<Character, Double>> mappings = new ArrayList<>();
        Map<Character, Double> map1 = new HashMap<>();
        map1.put('p', 100.0);
        map1.put('q', 200.0);
        Map<Character, Double> map2 = new HashMap<>();
        map2.put('r', -10.0);
        map2.put('s', -20.0);
        mappings.add(map1);
        mappings.add(map2);
        
        fromMappingsInputMapper = InputMapper.fromMappings(mappings);
    }

    @Test
    void testMakeFactory() {
        // Test the make factory method
        assertEquals(2, inputMapper.size());
        
        // Check first mapping
        Map<Character, Double> firstMap = inputMapper.get(0);
        assertEquals(3, firstMap.size());
        assertEquals(10.0, firstMap.get('a'));
        assertEquals(20.0, firstMap.get('b'));
        assertEquals(30.0, firstMap.get('c'));
        
        // Check second mapping
        Map<Character, Double> secondMap = inputMapper.get(1);
        assertEquals(3, secondMap.size());
        assertEquals(-5.0, secondMap.get('a'));
        assertEquals(0.0, secondMap.get('b'));
        assertEquals(5.0, secondMap.get('c'));
    }

    @Test
    void testMakeWithCustomCharsFactory() {
        // Test the makeWithCustomChars factory method
        assertEquals(2, customCharInputMapper.size());
        
        // Check first mapping
        Map<Character, Double> firstMap = customCharInputMapper.get(0);
        assertEquals(3, firstMap.size());
        assertEquals(10.0, firstMap.get('x'));
        assertEquals(20.0, firstMap.get('y'));
        assertEquals(30.0, firstMap.get('z'));
        
        // Check second mapping
        Map<Character, Double> secondMap = customCharInputMapper.get(1);
        assertEquals(3, secondMap.size());
        assertEquals(-5.0, secondMap.get('y'));
        assertEquals(0.0, secondMap.get('z'));
        assertEquals(5.0, secondMap.get('{'));
    }

    @Test
    void testFromMappingsFactory() {
        // Test the fromMappings factory method
        assertEquals(2, fromMappingsInputMapper.size());
        
        // Check first mapping
        Map<Character, Double> firstMap = fromMappingsInputMapper.get(0);
        assertEquals(2, firstMap.size());
        assertEquals(100.0, firstMap.get('p'));
        assertEquals(200.0, firstMap.get('q'));
        
        // Check second mapping
        Map<Character, Double> secondMap = fromMappingsInputMapper.get(1);
        assertEquals(2, secondMap.size());
        assertEquals(-10.0, secondMap.get('r'));
        assertEquals(-20.0, secondMap.get('s'));
    }

    @Test
    void testListInterfaceMethods() {
        // Test size method
        assertEquals(2, inputMapper.size());
        
        // Test isEmpty method
        assertFalse(inputMapper.isEmpty());
        
        // Test contains method
        Map<Character, Double> firstMap = inputMapper.get(0);
        assertTrue(inputMapper.contains(firstMap));
        
        // Test iterator method
        Iterator<Map<Character, Double>> iterator = inputMapper.iterator();
        assertTrue(iterator.hasNext());
        assertEquals(firstMap, iterator.next());
        
        // Test toArray method
        Object[] array = inputMapper.toArray();
        assertEquals(2, array.length);
        assertEquals(firstMap, array[0]);
        
        // Test toArray(T[] a) method
        Map<Character, Double>[] typedArray = inputMapper.toArray(new Map[0]);
        assertEquals(2, typedArray.length);
        assertEquals(firstMap, typedArray[0]);
        
        // Test add and remove methods
        Map<Character, Double> newMap = new HashMap<>();
        newMap.put('d', 40.0);
        assertTrue(inputMapper.add(newMap));
        assertEquals(3, inputMapper.size());
        assertEquals(newMap, inputMapper.get(2));
        assertTrue(inputMapper.remove(newMap));
        assertEquals(2, inputMapper.size());
        
        // Test containsAll method
        List<Map<Character, Double>> subList = new ArrayList<>();
        subList.add(firstMap);
        assertTrue(inputMapper.containsAll(subList));
        
        // Test addAll method
        List<Map<Character, Double>> newMaps = new ArrayList<>();
        Map<Character, Double> newMap1 = new HashMap<>();
        newMap1.put('d', 40.0);
        Map<Character, Double> newMap2 = new HashMap<>();
        newMap2.put('e', 50.0);
        newMaps.add(newMap1);
        newMaps.add(newMap2);
        assertTrue(inputMapper.addAll(newMaps));
        assertEquals(4, inputMapper.size());
        assertEquals(newMap1, inputMapper.get(2));
        assertEquals(newMap2, inputMapper.get(3));
        
        // Test addAll at index method
        Map<Character, Double> newMap3 = new HashMap<>();
        newMap3.put('f', 60.0);
        List<Map<Character, Double>> moreNewMaps = new ArrayList<>();
        moreNewMaps.add(newMap3);
        assertTrue(inputMapper.addAll(1, moreNewMaps));
        assertEquals(5, inputMapper.size());
        assertEquals(newMap3, inputMapper.get(1));
        
        // Test removeAll method
        List<Map<Character, Double>> mapsToRemove = new ArrayList<>();
        mapsToRemove.add(newMap1);
        mapsToRemove.add(newMap2);
        assertTrue(inputMapper.removeAll(mapsToRemove));
        assertEquals(3, inputMapper.size());
        
        // Test retainAll method
        List<Map<Character, Double>> mapsToRetain = new ArrayList<>();
        mapsToRetain.add(firstMap);
        assertTrue(inputMapper.retainAll(mapsToRetain));
        assertEquals(1, inputMapper.size());
        assertEquals(firstMap, inputMapper.get(0));
        
        // Test clear method
        inputMapper.clear();
        assertTrue(inputMapper.isEmpty());
        assertEquals(0, inputMapper.size());
    }

    @Test
    void testGetSetAndIndexMethods() {
        // Test get method
        Map<Character, Double> firstMap = inputMapper.get(0);
        assertEquals(10.0, firstMap.get('a'));
        
        // Test set method
        Map<Character, Double> newMap = new HashMap<>();
        newMap.put('x', 100.0);
        Map<Character, Double> oldMap = inputMapper.set(0, newMap);
        assertEquals(firstMap, oldMap);
        assertEquals(newMap, inputMapper.get(0));
        
        // Test add at index method
        Map<Character, Double> anotherMap = new HashMap<>();
        anotherMap.put('y', 200.0);
        inputMapper.add(0, anotherMap);
        assertEquals(anotherMap, inputMapper.get(0));
        assertEquals(newMap, inputMapper.get(1));
        
        // Test remove at index method
        Map<Character, Double> removedMap = inputMapper.remove(0);
        assertEquals(anotherMap, removedMap);
        assertEquals(newMap, inputMapper.get(0));
        
        // Test indexOf method
        assertEquals(0, inputMapper.indexOf(newMap));
        
        // Test lastIndexOf method
        inputMapper.add(newMap);
        assertEquals(2, inputMapper.lastIndexOf(newMap));
    }

    @Test
    void testListIteratorMethods() {
        // Test listIterator method
        ListIterator<Map<Character, Double>> listIterator = inputMapper.listIterator();
        assertTrue(listIterator.hasNext());
        assertEquals(inputMapper.get(0), listIterator.next());
        
        // Test listIterator with index method
        ListIterator<Map<Character, Double>> indexedListIterator = inputMapper.listIterator(1);
        assertTrue(indexedListIterator.hasNext());
        assertEquals(inputMapper.get(1), indexedListIterator.next());
    }

    @Test
    void testSubListMethod() {
        // Test subList method
        List<Map<Character, Double>> subList = inputMapper.subList(0, 1);
        assertEquals(1, subList.size());
        assertEquals(inputMapper.get(0), subList.get(0));
    }

    @Test
    void testStreamMethods() {
        // Test stream method
        List<Map<Character, Double>> streamResult = inputMapper.stream()
                .filter(map -> map.containsKey('a'))
                .toList();
        assertEquals(2, streamResult.size());
        
        // Test parallelStream method
        List<Map<Character, Double>> parallelStreamResult = inputMapper.parallelStream()
                .filter(map -> map.containsKey('a'))
                .toList();
        assertEquals(2, parallelStreamResult.size());
    }
}
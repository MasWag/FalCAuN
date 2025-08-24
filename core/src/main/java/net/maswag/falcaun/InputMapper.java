package net.maswag.falcaun;

import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * A class that represents a mapping from characters to double values.
 * This class implements List&lt;Map&lt;Character, Double&gt;&gt; and can be constructed
 * from a List&lt;List&lt;Double&gt;&gt;, similar to how InputMapperReader works.
 * <p>
 * The InputMapper provides functionality to create a list of character-to-double mappings
 * from a list of lists of double values. Each inner list in the input is converted to a map
 * where characters (starting from 'a') are assigned to the double values.
 * </p>
 */
public class InputMapper implements List<Map<Character, Double>> {
    
    private final ArrayList<Map<Character, Double>> delegate;
    
    /**
     * Private constructor used by factory methods.
     * 
     * @param delegate The ArrayList to delegate to
     */
    private InputMapper(ArrayList<Map<Character, Double>> delegate) {
        this.delegate = delegate;
    }
    
    // List interface implementation methods
    
    @Override
    public int size() {
        return delegate.size();
    }
    
    @Override
    public boolean isEmpty() {
        return delegate.isEmpty();
    }
    
    @Override
    public boolean contains(Object o) {
        return delegate.contains(o);
    }
    
    @Override
    public @NotNull Iterator<Map<Character, Double>> iterator() {
        return delegate.iterator();
    }
    
    @Override
    public Object @NotNull [] toArray() {
        return delegate.toArray();
    }
    
    @Override
    public <T> T @NotNull [] toArray(T[] a) {
        return delegate.toArray(a);
    }
    
    @Override
    public boolean add(Map<Character, Double> characterDoubleMap) {
        return delegate.add(characterDoubleMap);
    }
    
    @Override
    public boolean remove(Object o) {
        return delegate.remove(o);
    }
    
    @Override
    public boolean containsAll(Collection<?> c) {
        return delegate.containsAll(c);
    }
    
    @Override
    public boolean addAll(Collection<? extends Map<Character, Double>> c) {
        return delegate.addAll(c);
    }
    
    @Override
    public boolean addAll(int index, Collection<? extends Map<Character, Double>> c) {
        return delegate.addAll(index, c);
    }
    
    @Override
    public boolean removeAll(Collection<?> c) {
        return delegate.removeAll(c);
    }
    
    @Override
    public boolean retainAll(Collection<?> c) {
        return delegate.retainAll(c);
    }
    
    @Override
    public void clear() {
        delegate.clear();
    }
    
    @Override
    public Map<Character, Double> get(int index) {
        return delegate.get(index);
    }
    
    @Override
    public Map<Character, Double> set(int index, Map<Character, Double> element) {
        return delegate.set(index, element);
    }
    
    @Override
    public void add(int index, Map<Character, Double> element) {
        delegate.add(index, element);
    }
    
    @Override
    public Map<Character, Double> remove(int index) {
        return delegate.remove(index);
    }
    
    @Override
    public int indexOf(Object o) {
        return delegate.indexOf(o);
    }
    
    @Override
    public int lastIndexOf(Object o) {
        return delegate.lastIndexOf(o);
    }
    
    @Override
    public @NotNull ListIterator<Map<Character, Double>> listIterator() {
        return delegate.listIterator();
    }
    
    @Override
    public @NotNull ListIterator<Map<Character, Double>> listIterator(int index) {
        return delegate.listIterator(index);
    }
    
    @Override
    public @NotNull List<Map<Character, Double>> subList(int fromIndex, int toIndex) {
        return delegate.subList(fromIndex, toIndex);
    }
    
    @Override
    public void replaceAll(@NotNull UnaryOperator<Map<Character, Double>> operator) {
        delegate.replaceAll(operator);
    }
    
    @Override
    public void sort(Comparator<? super Map<Character, Double>> c) {
        delegate.sort(c);
    }
    
    @Override
    public @NotNull Spliterator<Map<Character, Double>> spliterator() {
        return delegate.spliterator();
    }
    
    @Override
    public boolean removeIf(@NotNull Predicate<? super Map<Character, Double>> filter) {
        return delegate.removeIf(filter);
    }
    
    @Override
    public @NotNull Stream<Map<Character, Double>> stream() {
        return delegate.stream();
    }
    
    @Override
    public @NotNull Stream<Map<Character, Double>> parallelStream() {
        return delegate.parallelStream();
    }
    
    @Override
    public void forEach(Consumer<? super Map<Character, Double>> action) {
        delegate.forEach(action);
    }
    
    /**
     * Creates an InputMapper from a List&lt;List&lt;Double&gt;&gt;.
     * This is a static factory method similar to InputMapperReader.make().
     * Each inner list is converted to a map where characters (starting from 'a')
     * are assigned to the double values.
     *
     * @param data The list of lists of double values to convert
     * @return A new InputMapper instance
     */
    public static InputMapper make(List<List<Double>> data) {
        char[] charList = new char[data.size()];
        Arrays.fill(charList, 'a');
        
        return new InputMapper(AbstractMapperReader.assignCharacters(data, charList));
    }
    
    /**
     * Creates an InputMapper from a List&lt;List&lt;Double&gt;&gt; with custom starting characters.
     * Each inner list is converted to a map where characters (starting from the specified characters)
     * are assigned to the double values.
     *
     * @param data     The list of lists of double values to convert
     * @param charList The array of starting characters for each list
     * @return A new InputMapper instance
     */
    public static InputMapper makeWithCustomChars(List<List<Double>> data, char[] charList) {
        return new InputMapper(AbstractMapperReader.assignCharacters(data, charList));
    }
    
    /**
     * Creates an InputMapper from an existing List&lt;Map&lt;Character, Double&gt;&gt;.
     * This is a static factory method to create an InputMapper from an existing mapping.
     *
     * @param mappings The list of character-to-double mappings
     * @return A new InputMapper instance
     */
    public static InputMapper fromMappings(List<Map<Character, Double>> mappings) {
        return new InputMapper(new ArrayList<>(mappings));
    }
    
    @Override
    public <T> T[] toArray(@NotNull IntFunction<T[]> generator) {
        return delegate.toArray(generator);
    }
}
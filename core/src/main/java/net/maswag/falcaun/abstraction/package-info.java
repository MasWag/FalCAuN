/**
 * Mappings between the concrete signals and the finite abstract alphabets used in automata learning.
 *
 * <p>{@link net.maswag.falcaun.abstraction.SignalDiscretizer} is the interface of such mappings. Its main
 * implementations are {@link net.maswag.falcaun.abstraction.NumericSULMapper},
 * {@link net.maswag.falcaun.abstraction.SignalAdapter}, and the specification-guided
 * {@link net.maswag.falcaun.abstraction.NumericSULMapperWithSGA}. The thresholds for the discretization are given
 * by {@link net.maswag.falcaun.abstraction.InputMapper} and {@link net.maswag.falcaun.abstraction.OutputMapper},
 * which can be read from files with {@link net.maswag.falcaun.abstraction.InputMapperReader} and
 * {@link net.maswag.falcaun.abstraction.OutputMapperReader}.</p>
 */
package net.maswag.falcaun.abstraction;

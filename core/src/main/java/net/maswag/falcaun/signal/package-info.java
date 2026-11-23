/**
 * Concrete numerical signals and derived signals.
 *
 * <p>{@link net.maswag.falcaun.signal.IOSignal} represents a pair of input and output signals, implemented by
 * {@link net.maswag.falcaun.signal.IODiscreteSignal} and {@link net.maswag.falcaun.signal.IOContinuousSignal}.
 * {@link net.maswag.falcaun.signal.Signal} is a timed sequence of numerical values.
 * {@link net.maswag.falcaun.signal.SignalMapper} and its implementations construct derived signals from the
 * concrete signals, e.g., {@link net.maswag.falcaun.signal.SimpleSignalMapper} and
 * {@link net.maswag.falcaun.signal.ExtendedSignalMapper}.</p>
 */
package net.maswag.falcaun.signal;

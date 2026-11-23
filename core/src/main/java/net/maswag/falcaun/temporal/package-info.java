/**
 * Temporal-logic specifications, their robustness semantics, and the management of the specifications.
 *
 * <p>{@link net.maswag.falcaun.temporal.TemporalLogic} is the interface of the STL and LTL formulas.
 * Formulas are usually constructed by parsing strings with {@link net.maswag.falcaun.temporal.STLFactory} or
 * {@link net.maswag.falcaun.temporal.LTLFactory}. The specifications to verify are managed by an
 * {@link net.maswag.falcaun.temporal.AdaptiveSTLUpdater}, e.g., {@link net.maswag.falcaun.temporal.StaticSTLList} or
 * the strengthening {@link net.maswag.falcaun.temporal.AdaptiveSTLList}.</p>
 */
package net.maswag.falcaun.temporal;

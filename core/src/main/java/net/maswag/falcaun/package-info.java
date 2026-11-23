/**
 * FalCAuN - Falsification of Cyber-Physical Systems via Automata Learning.
 *
 * <p>This package contains the system-under-test (SUT) interfaces, which are the main extension points of FalCAuN:
 * {@link net.maswag.falcaun.NumericSUL} for systems executed step by step with discrete-time signals and
 * {@link net.maswag.falcaun.ContinuousNumericSUL} for systems that also expose continuous-time outputs.
 * Backends such as Simulink and Python implement these interfaces in their own modules.</p>
 *
 * <p>The other abstractions are organized in the following subpackages.</p>
 * <ul>
 *     <li>{@link net.maswag.falcaun.signal}: concrete input/output signals and derived signals.</li>
 *     <li>{@link net.maswag.falcaun.abstraction}: the mappings between concrete signals and the finite abstract
 *     alphabets used by automata learning, e.g., {@link net.maswag.falcaun.abstraction.SignalDiscretizer}.</li>
 *     <li>{@link net.maswag.falcaun.temporal}: STL/LTL specifications, their robustness semantics, and the lists of
 *     specifications to falsify.</li>
 *     <li>{@link net.maswag.falcaun.oracle}: membership and equivalence oracles, including the robustness-guided
 *     equivalence testing.</li>
 *     <li>{@link net.maswag.falcaun.verification}: the black-box checking process combining the above, e.g.,
 *     {@link net.maswag.falcaun.verification.NumericSULVerifier}, and its result
 *     {@link net.maswag.falcaun.verification.VerificationResult}.</li>
 * </ul>
 *
 * <p>A typical use is: implement or obtain a {@code NumericSUL}, define a
 * {@link net.maswag.falcaun.abstraction.SignalDiscretizer} (e.g., {@link net.maswag.falcaun.abstraction.NumericSULMapper}),
 * parse the specifications with {@link net.maswag.falcaun.temporal.STLFactory} into an
 * {@link net.maswag.falcaun.temporal.AdaptiveSTLList}, and run a
 * {@link net.maswag.falcaun.verification.NumericSULVerifier} with some equivalence oracles.</p>
 *
 * <p>{@link net.maswag.falcaun.ArgParser} is the option parser of the legacy command-line interface.</p>
 */
package net.maswag.falcaun;

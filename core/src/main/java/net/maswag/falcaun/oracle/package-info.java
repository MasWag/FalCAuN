/**
 * Membership and equivalence oracles used in black-box checking.
 *
 * <p>{@link net.maswag.falcaun.oracle.NumericMembershipOracle} answers membership queries by executing a
 * {@link net.maswag.falcaun.NumericSUL} and caches the abstract outputs and the robustness values.
 * The robustness-guided equivalence oracles, e.g., {@link net.maswag.falcaun.oracle.HillClimbingEQOracle},
 * {@link net.maswag.falcaun.oracle.SAEQOracle}, and {@link net.maswag.falcaun.oracle.GAEQOracle}, search for
 * counterexamples minimizing the robustness obtained through a {@link net.maswag.falcaun.oracle.RobustnessOracle}.
 * They are usually configured through {@link net.maswag.falcaun.verification.NumericSULVerifier} rather than
 * constructed directly.</p>
 */
package net.maswag.falcaun.oracle;

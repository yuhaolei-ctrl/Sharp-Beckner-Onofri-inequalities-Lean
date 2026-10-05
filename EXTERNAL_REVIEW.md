# External semantic review packet

Review the exact Git commit, `SOURCE_MANIFEST.json`, the paper SHA-256, and
`audit/paper2_statement_map.json`. Record reviewer identity, date, reviewed
commit, inspected definitions, clause-level conclusions, and unresolved items.
No independent review is represented as completed by merely distributing this packet.

For every mapped result, compare the natural statement with the expanded Lean
type, including all imported predicates. Check quantifier order, parameter
ranges, actual function spaces and measures, finite versus infinite entropy,
extended sums, exact constants, equality almost everywhere, attainment,
uniformity in parameters, and existential witnesses shared between clauses.

Focus on the new density endpoints and `Paper2Definitions`: the finite case
must agree with the actual entropy integral; the infinite case must use top,
and a divergent Fourier sum must not become a default real zero. Verify
`negativeSobolevEnergy_fourier` against the paper's explicit Fourier convention.

For the mixed Friedrichs lemma, the current audit marks a missing unit-period
coordinate/form/domain transport. Do not approve that exact statement based
only on `physicalSpectralPowerGraph_scaling` or the historical angular target.
Retain the separate periodization, counterexample and cutoff-rate limitations.

For dimensions 1–10 inspect `LowDimensionRaw`, `LowDimensionConsequences`,
`Legacy/BecknerOnofri/LowDimensionComplete.lean`, and the relevant rational
certificate semantics. `Legacy` is a proof namespace, not a trusted axiom.

Comparator can establish equality of Lean statements and their definitions
between the trusted challenge and the solution. Axiom audits and kernel
checks establish properties of formal proofs. None of these checks establishes
natural-language correspondence, and same-assistant rereading is not an
independent external review.

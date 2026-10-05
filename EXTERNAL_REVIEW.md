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

The new clauses have a detailed object-level crosswalk in
[audit/NEW_ANALYTIC_CLAUSES.md](audit/NEW_ANALYTIC_CLAUSES.md).

For the mixed Friedrichs lemma, inspect the actual unit-period spaces in
`Paper2PhysicalMeasure`, both core transports in `Paper2PhysicalCore`, the
closure and operator graph equivalences, the unitary in `Paper2PhysicalLp`,
and the final `Physical.FractionalIntertwining` definition. The preserved
`physicalSpectralPowerGraph_scaling` helper alone is not the literal statement.
Check that inactive coordinates keep both periodic parity sectors and that
physical spectral powers act on the actual physical L² space.

For periodization inspect `Paper2PeriodizationDefinitions` and
`Paper2Periodization`: coordinate-line derivatives are iterated over every
finite list, translation is proved to commute, and the majorant is uniform
on each compact set. The sum consists of the original rational profile's
translated derivatives. Counterexample and cutoff-rate statements outside
the 51-result scope remain separately disclosed in `AUDIT_ZH.md`.

For dimensions 1–10 inspect `LowDimensionRaw`, `LowDimensionConsequences`,
`Legacy/BecknerOnofri/LowDimensionComplete.lean`, and the relevant rational
certificate semantics. `Legacy` is a proof namespace, not a trusted axiom.

Comparator can establish equality of Lean statements and their definitions
between the trusted challenge and the solution. Axiom audits and kernel
checks establish properties of formal proofs. None of these checks establishes
natural-language correspondence, and same-assistant rereading is not an
independent external review.

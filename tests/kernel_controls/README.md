# Independent-kernel controls

`valid.ndjson.gz` is the Lean 4.32.0 export of
`tests/comparator_controls/Solution.lean`, whose theorem is `2 + 2 = 4`.
The export includes the standard axioms and Comparator's primitive roots.
`manifest.json` records raw and compressed identities and the exporter revision.

`invalid.ndjson.gz` has the same declarations, except the `certificateControl`
theorem's proof value is replaced by the expression of its proposition. This
is deliberately ill-typed. It must be rejected by a proof checker, while the
valid export must be accepted. The real manuscript certificate is not modified.

The Nanoda runtime adapter also passed these controls; its exact-once trace
inventory and actual outcomes are in `verification/current/nanoda-runtime-control`.
Fixture success is not a result for the 269-target manuscript corpus.

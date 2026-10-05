# Verification of the Palomar adaptation

This branch uses Lean 4.35.0-rc2. The original Lean 4.32.0 certificate is
historical evidence only; none of its success records certify migrated code.

Run the structural preflight and select one candidate configuration:

```sh
python3 scripts/audit_palomar.py
python3 scripts/verify_palomar.py Palomar/comparator-lowdim.json
python3 scripts/verify_palomar.py Palomar/comparator-highdim.json
python3 scripts/verify_palomar.py Palomar/comparator-eleven.json
```

Each verification command builds the selected Challenge and Solution and
checks the transitive axioms of every selected theorem. Add `--comparator`
to run the toolchain's Comparator with the configured NanoDa replay. On a
non-Linux development host, `--development` explicitly disables its sandbox;
that local check does not provide Palomar's protected verification environment.

The three candidate configurations use the same root `formalization.yaml`.
Each submission must select one configuration and an immutable full commit SHA.
Palomar performs its own source, toolchain, dependency, metadata, licence,
mechanical, and editorial checks. The local structural script is supplementary,
not a replacement for those checks.

Results and actual exit codes are written to ignored `verification/runs/`.
Migration logs are kept outside the public source repository. The concise
current status is in `STATUS.json`; it must not report success for a pending
or failed build. The original source manifests and export descriptors retain
their historical identities and are not rewritten to make the migration pass.

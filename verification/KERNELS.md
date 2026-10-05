# Kernel validation

The official Lean kernel and Nanoda are different implementations. Comparator's
default-kernel replay is an additional replay by the **official** kernel, not
itself an independent kernel. The historical configuration disables Nanoda.

The current checker source is pinned to Nanoda
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built with Rust 1.90.0.
The one source patch raises `STACK_SIZE` from 16,777,216 to 268,435,456 bytes,
as in the Arena recipe. Our configuration uses two worker threads and a strict
axiom allow-list, instead of Arena's permissive all-axioms setting.
`unpermitted_axiom_hard_error=false` only skips unused exported axioms; a proof
referring to one still fails. `unsafe_permit_all_axioms` remains false.

```sh
git clone https://github.com/ammkrn/nanoda_lib .tools/nanoda
git -C .tools/nanoda checkout 4c544ed4099c8227f07d5de77ad1e69fb0740a27
python3 - <<'PY'
from pathlib import Path
p = Path('.tools/nanoda/src/lib.rs')
s = p.read_text()
assert 'STACK_SIZE: usize = 16_777_216;' in s
p.write_text(s.replace('STACK_SIZE: usize = 16_777_216;',
                       'STACK_SIZE: usize = 268_435_456;'))
PY
cargo build --release --locked --manifest-path .tools/nanoda/Cargo.toml
python3 scripts/check_nanoda.py --binary .tools/nanoda/target/release/nanoda_bin
```

The proof export is large. The script records source configuration, exact target
list, exporter result, binary digest, export digest and checker exit code.
The current `STATUS.json` distinguishes the actual baseline check from any
unexecuted full paper-2 check. Never replace an uncompleted run by this recipe.

Alternatively set `enable_nanoda` to true in a separately named Comparator
configuration and set `COMPARATOR_NANODA` to the absolute binary path. This
checks matching and both kernels in one workflow.

The control fixture in `tests/comparator_controls` has a matching true theorem
and a different true theorem under the same name. The matching configuration
must be accepted by both kernels; the mismatch must be rejected by Comparator.
These are tool checks, not acceptance of the Beckner–Onofri corpus.

## Lean Kernel Arena

Primary documentation:
[Arena](https://arena.lean-lang.org/),
[contribution interface](https://github.com/leanprover/lean-kernel-arena),
[Nanoda recipe](https://github.com/leanprover/lean-kernel-arena/blob/master/checkers/nanoda.yaml),
[test schema](https://github.com/leanprover/lean-kernel-arena/blob/master/schemas/test.json).

Generate a proposed module test after publication:

```sh
python3 scripts/arena_test.py --revision "$(git rev-parse HEAD)" > beckner-onofri.yaml
```

JSON syntax is valid YAML. The descriptor pins the source revision and runs the
dependency bootstrap before exporting only the registered declarations.
Arena's exporter/Lean version must be compatible with Lean 4.32.0; migrating
this certificate to another toolchain requires a separate checked change.
The descriptor is preparation for an external run, not a submitted or accepted
Arena result. No Arena pull request or website entry has been created.

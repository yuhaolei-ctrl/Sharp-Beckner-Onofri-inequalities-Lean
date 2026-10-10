module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Final
public import BecknerOnofri.V2.Reaudit.Sobolev.Branch

@[expose] public section

/-! # Statement-level bridge to `Sobolev.Section5QuarticReduction`

`Final.lean` proves the three assertions of `lem:section5-quartic-reduction` for the Sobolev graph
without importing `Sobolev.Branch`.  This module only records that the proposition proved there is
*the same proposition* as `Sobolev.Section5QuarticReduction`, so that the previous worker's
transported theorem `Sobolev.section5_quartic_reduction` can be replaced by the native one.  The
native theorem does not depend on `graph_toComplement`. -/

noncomputable section
namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-- `Sobolev.Section5QuarticReduction` for the Sobolev graph, proved natively (statement
identical to the one proved by the transported theorem `Sobolev.section5_quartic_reduction`). -/
theorem section5_quartic_reduction_native' (hd11 : 11 ≤ d) :
    Section5QuarticReduction d s (graph (s := s) hd11) :=
  section5_quartic_reduction_native hd11

end BecknerOnofri.V2.Reaudit.SobolevQuartic

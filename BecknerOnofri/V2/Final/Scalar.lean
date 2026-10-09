module

public import BecknerOnofri.V2.Interval.FamilyScalar
public import BecknerOnofri.V2.Assembly.Hypotheses

@[expose] public section

/-! # `ScalarBounds` from the three finite interval checks (Final package)

`Assembly.ScalarBounds` is the printed statement of Lemma 5.21 (`d12-spin-lem:scalar`).
`Interval.family_scalar_bounds` proves it (with one extra strict-variance conjunct) from the three
finite computations `Row.checkCell` on all cells of `row1`, `row2`, `row3`.  This file only drops the
extra conjunct. -/

noncomputable section
namespace BecknerOnofri.V2.Final

open BecknerOnofri.V2.Interval

/-- **Lemma 5.21 (`d12-spin-lem:scalar`)** from the three finite checks. -/
theorem scalarBounds_of_checks
    (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    BecknerOnofri.V2.Assembly.ScalarBounds := by
  intro t ht0 ht1
  obtain ⟨hf, hv, he⟩ := family_scalar_bounds hc1 hc2 hc3 t ht0 ht1
  exact ⟨hf, hv.1, he⟩

#print axioms scalarBounds_of_checks

end BecknerOnofri.V2.Final

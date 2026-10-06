module

public import BecknerOnofri.SpinReferenceDefinitions
public import BecknerOnofri.CircleGammaDefinitions

@[expose] public section

/-!
# The two remaining numerical inputs for dimension twelve

* Lemma 5.17 (lem:section5-global-small-gamma): `ψ ≤ γ` on `[0,1)`.
* Lemma 5.19 (lem:section5-scalar-pressure), on `[1/16, 0.99]`: `𝓑(t) > t⁴/200`.

PENDING: both proofs are being attached; this file must contain no `sorry` before release.
-/

noncomputable section

open Set

namespace BecknerOnofri.HighDim

/-- Lemma 5.17. -/
theorem psi_le_gamma : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t := by
  sorry

/-- Lemma 5.19 on `[1/16, 0.99]`. -/
theorem pressureScalar_gt : ∀ t ∈ Icc (1 / 16 : ℝ) (99 / 100), t ^ 4 / 200 < Spin.pressureScalar t := by
  sorry

end BecknerOnofri.HighDim

module

public import BecknerOnofri.SpinReferenceDefinitions
public import BecknerOnofri.CircleGammaPsi
public import BecknerOnofri.SpinPressureCertificateCover

@[expose] public section

/-!
# The two remaining numerical inputs for dimension twelve

* Lemma 5.17 (lem:section5-global-small-gamma): `ψ ≤ γ` on `[0,1)`.
* Lemma 5.20 (lem:section5-scalar-pressure), on `[1/16, 0.99]`: `𝓑(t) > t⁴/200`.

The first is `CircleScalar.psi_le_gamma` (Bernstein certificates), the second
`Spin.PressureCertificate.pressureScalar_gt_cells` (Taylor-model certificate on 127 cells).
-/

noncomputable section

open Set

namespace BecknerOnofri.HighDim

/-- Lemma 5.17. -/
theorem psi_le_gamma : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t :=
  fun t ht => CircleScalar.psi_le_gamma t ht.1 ht.2

/-- Lemma 5.20 on `[1/16, 0.99]`. -/
theorem pressureScalar_gt :
    ∀ t ∈ Icc (1 / 16 : ℝ) (99 / 100), t ^ 4 / 200 < Spin.pressureScalar t :=
  Spin.PressureCertificate.pressureScalar_gt_cells

end BecknerOnofri.HighDim

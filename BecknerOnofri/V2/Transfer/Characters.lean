module

public import BecknerOnofri.Definitions

@[expose] public section

/-! # Elementary facts on the characters `UnitAddTorus.mFourier` used in the transfer package. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma norm_mFourier_apply {d : ℕ} (n : Frequency d) (x : Torus d) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  simp [UnitAddTorus.mFourier, norm_prod]

lemma continuous_mFourier' {d : ℕ} (n : Frequency d) :
    Continuous (UnitAddTorus.mFourier n : Torus d → ℂ) := (UnitAddTorus.mFourier n).continuous

lemma integrable_of_continuous_torus {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Torus d → E} (hf : Continuous f) : Integrable f (torusMeasure d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of a character is the Kronecker delta at the zero frequency. -/
theorem integral_mFourier {d : ℕ} (n : Frequency d) :
    ∫ x, UnitAddTorus.mFourier n x ∂torusMeasure d = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) (-n) 0
  simp only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply,
    one_mul, ← UnitAddTorus.mFourier_neg, neg_neg, neg_eq_zero] at h
  simpa [torusMeasure, volume] using h

theorem mFourier_congr_support {d : ℕ} (n : Frequency d) {z z' : Torus d}
    (h : ∀ i, n i ≠ 0 → z i = z' i) :
    UnitAddTorus.mFourier n z = UnitAddTorus.mFourier n z' := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hi : n i = 0
  · simp [hi]
  · rw [h i hi]

end BecknerOnofri.V2.Transfer

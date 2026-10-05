import PhysicalMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set MeasureTheory.Lp MeasureTheory.Measure
open scoped ENNReal
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial

lemma ae_weight {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {r : ℝ} (hr : 0 < r) {p : X → Prop} :
    (∀ᵐ x ∂ENNReal.ofReal r • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
  simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero,
    ne_of_gt (ENNReal.ofReal_pos.mpr hr), false_or]

section Rescale
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (r : ℝ) (hr : 0 < r)
include hr in
private lemma rescale_bound : μ ≤ (ENNReal.ofReal r)⁻¹ • (ENNReal.ofReal r • μ) := by
  rw [smul_smul, ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top, one_smul]

def rescaleForward : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ENNReal.ofReal r • μ) :=
  LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top le_rfl

def rescaleBackward : Lp ℝ 2 (ENNReal.ofReal r • μ) →L[ℝ] Lp ℝ 2 μ :=
  LpToLpOfMeasureLeSMul (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hr)))
    (rescale_bound μ r hr)

include hr in
lemma rescaleForward_ae (f : Lp ℝ 2 μ) :
    rescaleForward μ r f =ᵐ[μ] f :=
  (ae_weight hr).mp
    (coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top le_rfl f)
lemma rescaleBackward_ae (f : Lp ℝ 2 (ENNReal.ofReal r • μ)) :
    rescaleBackward μ r hr f =ᵐ[μ] f :=
  coeFn_LpToLpOfMeasureLeSMul _ (rescale_bound μ r hr) f

def rescaleEquiv : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 (ENNReal.ofReal r • μ) where
  toFun := rescaleForward μ r
  invFun := rescaleBackward μ r hr
  map_add' := (rescaleForward μ r).map_add
  map_smul' := (rescaleForward μ r).map_smul
  left_inv f := by
    apply Lp.ext
    exact (rescaleBackward_ae μ r hr _).trans (rescaleForward_ae μ r hr f)
  right_inv f := by
    apply Lp.ext
    apply (ae_weight hr).mpr
    exact (rescaleForward_ae μ r hr _).trans (rescaleBackward_ae μ r hr f)
  continuous_toFun := (rescaleForward μ r).continuous
  continuous_invFun := (rescaleBackward μ r hr).continuous
end Rescale

def coordinateEquiv (d : ℕ) : Space d ≃ᵐ Space d where
  toFun := down
  invFun := up
  left_inv := up_down
  right_inv := down_up
  measurable_toFun := by change Measurable down; unfold down; fun_prop
  measurable_invFun := by change Measurable up; unfold up; fun_prop

lemma down_preserving {d : ℕ} (α : MultiIndex d) :
    MeasurePreserving (coordinateEquiv d)
      (Friedrichs.MixedSpatial.spatialMeasure α) (ENNReal.ofReal (scale^d) • spatialMeasure α) :=
  ⟨(coordinateEquiv d).measurable, map_spatial α⟩
lemma up_preserving {d : ℕ} (α : MultiIndex d) :
    MeasurePreserving (coordinateEquiv d).symm
      (ENNReal.ofReal (scale^d) • spatialMeasure α) (Friedrichs.MixedSpatial.spatialMeasure α) :=
  (down_preserving α).symm _

/-- Change of coordinates on L² with the Jacobian-weighted physical measure. -/
def weightedCoordinateEquiv {d : ℕ} (α : MultiIndex d) :
    Friedrichs.MixedSpatial.H α ≃L[ℝ] Lp ℝ 2 (ENNReal.ofReal (scale^d) • spatialMeasure α) where
  toFun := Lp.compMeasurePreservingₗᵢ ℝ _ (up_preserving α)
  invFun := Lp.compMeasurePreservingₗᵢ ℝ _ (down_preserving α)
  map_add' := (Lp.compMeasurePreservingₗᵢ ℝ _ (up_preserving α)).map_add
  map_smul' := (Lp.compMeasurePreservingₗᵢ ℝ _ (up_preserving α)).map_smul
  left_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using Lp.compMeasurePreserving_id_apply f
  continuous_toFun := (Lp.compMeasurePreservingₗᵢ ℝ _ (up_preserving α)).continuous
  continuous_invFun := (Lp.compMeasurePreservingₗᵢ ℝ _ (down_preserving α)).continuous

/-- Raw spatial pullback `f ↦ f(2πx)` on the actual unweighted L² spaces.
This is a continuous linear equivalence; its norm includes the Jacobian. -/
def coordinateLpEquiv {d : ℕ} (α : MultiIndex d) :
    Friedrichs.MixedSpatial.H α ≃L[ℝ] H α :=
  (weightedCoordinateEquiv α).trans
    (rescaleEquiv (spatialMeasure α) (scale^d) (pow_pos scale_pos d)).symm

lemma coordinateLpEquiv_ae {d : ℕ} (α : MultiIndex d) (f : Friedrichs.MixedSpatial.H α) :
    coordinateLpEquiv α f =ᵐ[spatialMeasure α] fun x => f (up x) := by
  have h₁ := rescaleBackward_ae (spatialMeasure α) (scale^d) (pow_pos scale_pos d)
    (weightedCoordinateEquiv α f)
  have h₂ := Lp.coeFn_compMeasurePreserving f (up_preserving α)
  exact h₁.trans ((ae_weight (pow_pos scale_pos d)).mp h₂)

lemma coordinateLpEquiv_symm_ae {d : ℕ} (α : MultiIndex d) (f : H α) :
    (coordinateLpEquiv α).symm f =ᵐ[Friedrichs.MixedSpatial.spatialMeasure α]
      fun x => f (down x) := by
  have h₁ := Lp.coeFn_compMeasurePreserving
    (rescaleForward (spatialMeasure α) (scale^d) f) (down_preserving α)
  have h₂ := coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (le_rfl : ENNReal.ofReal (scale^d) • spatialMeasure α ≤ ENNReal.ofReal (scale^d) • spatialMeasure α) f
  exact h₁.trans ((down_preserving α).quasiMeasurePreserving.ae h₂)

lemma coordinateLpEquiv_inner {d : ℕ} (α : MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H α) :
    scale^d * inner ℝ (coordinateLpEquiv α f) (coordinateLpEquiv α g) = inner ℝ f g := by
  have h := (up_preserving α).integral_comp' (fun x => inner ℝ (f x) (g x))
  rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_pos scale_pos d).le] at h
  rw [L2.inner_def, L2.inner_def]
  rw [← h]
  congr 1
  apply integral_congr_ae
  filter_upwards [coordinateLpEquiv_ae α f, coordinateLpEquiv_ae α g] with x hf hg
  rw [hf,hg]
  rfl

lemma up_ae {d : ℕ} {α : MultiIndex d} {p : Space d → Prop}
    (h : ∀ᵐ x ∂Friedrichs.MixedSpatial.spatialMeasure α, p x) :
    ∀ᵐ x ∂spatialMeasure α, p (up x) :=
  (ae_weight (pow_pos scale_pos d)).mp ((up_preserving α).quasiMeasurePreserving.ae h)
lemma down_ae {d : ℕ} {α : MultiIndex d} {p : Space d → Prop}
    (h : ∀ᵐ x ∂spatialMeasure α, p x) :
    ∀ᵐ x ∂Friedrichs.MixedSpatial.spatialMeasure α, p (down x) :=
  (down_preserving α).quasiMeasurePreserving.ae ((ae_weight (pow_pos scale_pos d)).mpr h)

/-- The genuinely unitary coordinate map for the unweighted Lebesgue spaces:
`f(x) ↦ (2π)^(d/2) f(2πx)`, with the prefactor written as a square root. -/
def coordinateUnitary {d : ℕ} (α : MultiIndex d) : Friedrichs.MixedSpatial.H α ≃ₗᵢ[ℝ] H α where
  toLinearEquiv := (coordinateLpEquiv α).toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (H α) (Real.sqrt (scale^d))
      (Real.sqrt_pos.mpr (pow_pos scale_pos d)).ne')
  norm_map' f := by
    change ‖Real.sqrt (scale^d) • coordinateLpEquiv α f‖ = ‖f‖
    have h := coordinateLpEquiv_inner α f f
    simp only [real_inner_self_eq_norm_sq] at h
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt (pow_pos scale_pos d).le]
    exact h

#print axioms coordinateUnitary
#print axioms coordinateLpEquiv
#print axioms coordinateLpEquiv_inner
end BecknerOnofri.Paper2.Physical

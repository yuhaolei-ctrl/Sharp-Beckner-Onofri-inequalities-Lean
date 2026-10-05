module

public import BecknerOnofri.ElevenVariational
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! On any convex set where the extended supremum is finite, its real value
is convex because every actual admissible competitor gives an affine function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim

lemma pressure_toReal_convexOn {d : ℕ} (hd : 0 < d) {S : Set ℝ} (hS : Convex ℝ S)
    (hfin : ∀ β ∈ S, pressure d β = ((pressure d β).toReal:EReal)) :
    ConvexOn ℝ S (fun β => (pressure d β).toReal) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hS hx hy ha hb hab
  have hval (β : ℝ) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
      pressureValue β ρ = ((β/(2*spectralThreshold d)*(∑' k, spectralTerm ρ k)-entropy ρ:ℝ):EReal) := by
    unfold pressureValue
    rw [spectralEnergy_coe_eq_tsum hd ρ hρ]
    push_cast
    rfl
  apply EReal.coe_le_coe_iff.mp
  rw [← hfin _ hz]
  apply iSup_le fun ρ => iSup_le fun hρ => ?_
  have hx' : pressureValue x ρ ≤ pressure d x := le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
  have hy' : pressureValue y ρ ≤ pressure d y := le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
  rw [hval x ρ hρ, hfin x hx] at hx'
  rw [hval y ρ hρ, hfin y hy] at hy'
  have hxR := EReal.coe_le_coe_iff.mp hx'
  have hyR := EReal.coe_le_coe_iff.mp hy'
  change pressureValue (a • x+b • y) ρ ≤ _
  rw [hval _ ρ hρ]
  apply EReal.coe_le_coe_iff.mpr
  simp only [smul_eq_mul]
  have h := add_le_add (mul_le_mul_of_nonneg_left hxR ha) (mul_le_mul_of_nonneg_left hyR hb)
  have he : (a*x+b*y)/(2*spectralThreshold d)*(∑' k, spectralTerm ρ k)-entropy ρ =
      a*(x/(2*spectralThreshold d)*(∑' k, spectralTerm ρ k)-entropy ρ)+
        b*(y/(2*spectralThreshold d)*(∑' k, spectralTerm ρ k)-entropy ρ) := by
    linear_combination entropy ρ*hab
  rw [he]
  exact h

lemma defect_toReal_convexOn {d : ℕ} (hd : 0 < d) {S : Set ℝ} (hS : Convex ℝ S)
    (hfin : ∀ A ∈ S, coefficientDefect d A = ((coefficientDefect d A).toReal:EReal)) :
    ConvexOn ℝ S (fun A => (coefficientDefect d A).toReal) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hS hx hy ha hb hab
  apply EReal.coe_le_coe_iff.mp
  rw [← hfin _ hz]
  apply iSup_le fun u => iSup_le fun hu => ?_
  have hx' : logPartition u-((x*potentialEnergy u:ℝ):EReal) ≤ coefficientDefect d x :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have hy' : logPartition u-((y*potentialEnergy u:ℝ):EReal) ≤ coefficientDefect d y :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  rw [logPartition_eq_log_integral hd u hu, hfin x hx, ← EReal.coe_sub] at hx'
  rw [logPartition_eq_log_integral hd u hu, hfin y hy, ← EReal.coe_sub] at hy'
  rw [logPartition_eq_log_integral hd u hu, ← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  have h := add_le_add (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hx') ha)
    (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hy') hb)
  simp only [smul_eq_mul]
  linear_combination h - (Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d))*hab

#print axioms pressure_toReal_convexOn
#print axioms defect_toReal_convexOn
end BecknerOnofri.HighDim

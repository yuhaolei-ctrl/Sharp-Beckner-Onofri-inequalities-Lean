module

public import BecknerOnofri.PeriodizationCube
public import BecknerOnofri.Definitions
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Algebra.Order.Round

@[expose] public section

/-! # Row S006 (concentration test): the scaled mollifier on the torus

Printed (`eq:section2-concentrating-density`, `eq:section2-concentration-entropy`): for a probability
density `η` on `ℝ^d` supported in a ball around `0` of radius `< 1/2`, the function
`ρ_ε(x) = ε^{-d} η(x/ε)`, viewed on the fundamental domain `[-1/2, 1/2)^d` of `𝕋^d`, is a probability
density on the torus with `Ent(ρ_ε) = d log(1/ε) + ∫ η log η`.

Here `η` is any bounded measurable nonnegative function of integral `1` supported in the cube
`{|y_j| ≤ 1/4}` (the printed smooth bump function is a special case; smoothness is not used).  The
torus is identified with the fundamental cube through the representative map
`x ↦ circleRep (x_j)` into `[-1/2, 1/2)`, and the integral over the torus is converted to an integral
over the cube by `PeriodizationCube.quotient_measurePreserving`; the change of variables
`y ↦ ε⁻¹ y` is `Measure.integral_comp_inv_smul`. -/

noncomputable section
open MeasureTheory Set

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim

variable {d : ℕ}

/-- The representative in `[-1/2, 1/2)` of a point of the circle `ℝ/ℤ`. -/
def circleRep (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).val

/-- The representative in `[-1/2, 1/2)^d` of a point of the torus. -/
def torusRep (x : Torus d) : Fin d → ℝ := fun j => circleRep (x j)

lemma circleRep_mem (x : UnitAddCircle) : circleRep x ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := by
  have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  unfold circleRep
  simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using h

lemma coe_circleRep (x : UnitAddCircle) : ((circleRep x : ℝ) : UnitAddCircle) = x :=
  AddCircle.coe_equivIco

lemma circleRep_coe {y : ℝ} (hy : y ∈ Ico (-(1 / 2 : ℝ)) (1 / 2)) :
    circleRep (y : UnitAddCircle) = y := by
  unfold circleRep
  rw [AddCircle.equivIco_coe_eq (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using hy)]

lemma measurable_circleRep : Measurable circleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) (-(1 / 2 : ℝ))).measurable

lemma measurable_torusRep : Measurable (torusRep (d := d)) :=
  measurable_pi_iff.mpr (fun j => measurable_circleRep.comp (measurable_pi_apply j))

lemma measurable_scaledRep (c : ℝ) : Measurable (fun x : Torus d => c • torusRep x) :=
  measurable_torusRep.const_smul c

lemma norm_le_abs_circleRep (x : UnitAddCircle) : ‖x‖ ≤ |circleRep x| := by
  conv_lhs => rw [← coe_circleRep x]
  rw [UnitAddCircle.norm_eq]
  simpa using round_le (circleRep x) 0

lemma torusRep_coe {y : Fin d → ℝ} (hy : y ∈ PeriodizationCube.cube d) :
    torusRep (fun i => (y i : UnitAddCircle)) = y := by
  funext i
  exact circleRep_coe (hy i (mem_univ i))

/-- Integrals over the torus are integrals over the fundamental cube. -/
lemma integral_torus_eq_cube {F : Torus d → ℝ} (hF : Measurable F) :
    ∫ x, F x ∂torusMeasure d =
      ∫ y in PeriodizationCube.cube d, F (fun i => (y i : UnitAddCircle)) := by
  have hmp := PeriodizationCube.quotient_measurePreserving d
  conv_lhs => rw [← hmp.map_eq]
  exact integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)

/-- The scaled function `x ↦ ε^{-d} η(ε⁻¹ x)` on the torus. -/
def mollified (η : (Fin d → ℝ) → ℝ) (ε : ℝ) (x : Torus d) : ℝ :=
  (ε ^ d)⁻¹ * η (ε⁻¹ • torusRep x)

section Mollifier

variable {η : (Fin d → ℝ) → ℝ} {ε : ℝ}

/-- Change of variables: the mollification preserves the integral of every function supported in the
cube `{|y_j| ≤ 1/4}`. -/
lemma integral_mollified_scaling (G : (Fin d → ℝ) → ℝ) (hG : Measurable G)
    (hGs : ∀ y, G y ≠ 0 → ∀ j, |y j| ≤ 1 / 4) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x, (ε ^ d)⁻¹ * G (ε⁻¹ • torusRep x) ∂torusMeasure d = ∫ y, G y := by
  have hm : Measurable (fun x : Torus d => (ε ^ d)⁻¹ * G (ε⁻¹ • torusRep x)) :=
    measurable_const.mul (hG.comp (measurable_scaledRep _))
  rw [integral_torus_eq_cube hm]
  have h1 : ∫ y in PeriodizationCube.cube d, (ε ^ d)⁻¹ *
      G (ε⁻¹ • torusRep (fun i => (y i : UnitAddCircle))) =
      ∫ y in PeriodizationCube.cube d, (ε ^ d)⁻¹ * G (ε⁻¹ • y) := by
    apply setIntegral_congr_fun (PeriodizationCube.cube_measurable d)
    intro y hy
    simp only [torusRep_coe hy]
  rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
  · have h2 := Measure.integral_comp_inv_smul (volume : Measure (Fin d → ℝ)) G ε
    rw [Module.finrank_fin_fun] at h2
    rw [h2, abs_of_pos (pow_pos hε d), smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hε d).ne', one_mul]
  · intro y hy
    by_contra hne
    have hG0 : G (ε⁻¹ • y) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    apply hy
    intro i _
    have h3 := hGs _ hG0 i
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε] at h3
    have h4 : |y i| ≤ ε / 4 := by
      rw [inv_mul_le_iff₀ hε] at h3
      linarith
    have h5 := abs_le.mp (h4.trans (by linarith : ε / 4 ≤ 1 / 4))
    exact ⟨by linarith [h5.1], by linarith [h5.2]⟩

variable (hm : Measurable η) (hnn : ∀ y, 0 ≤ η y) (hs : ∀ y, η y ≠ 0 → ∀ j, |y j| ≤ 1 / 4)

include hm in
lemma measurable_mollified (ε : ℝ) : Measurable (mollified η ε : Torus d → ℝ) :=
  measurable_const.mul (hm.comp (measurable_scaledRep _))

include hnn in
lemma mollified_nonneg (hε : 0 < ε) (x : Torus d) : 0 ≤ mollified η ε x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le d)) (hnn _)

lemma mollified_le {M : ℝ} (hM : ∀ y, η y ≤ M) (hε : 0 < ε) (x : Torus d) :
    mollified η ε x ≤ (ε ^ d)⁻¹ * M :=
  mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr (pow_nonneg hε.le d))

include hs in
/-- Localization: the mollification vanishes outside the sup-ball of radius `ε/4`. -/
lemma mollified_support (hε : 0 < ε) {x : Torus d} (hx : mollified η ε x ≠ 0) :
    ∀ j, ‖x j‖ ≤ ε / 4 := by
  intro j
  have h1 : η (ε⁻¹ • torusRep x) ≠ 0 := fun h => hx (by simp [mollified, h])
  have h2 := hs _ h1 j
  simp only [torusRep, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε] at h2
  have h3 : |circleRep (x j)| ≤ ε / 4 := by
    rw [inv_mul_le_iff₀ hε] at h2
    linarith
  exact (norm_le_abs_circleRep (x j)).trans h3

include hm hs in
/-- The mollification has integral one when `η` does. -/
lemma integral_mollified (hmass : ∫ y, η y = 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x, mollified η ε x ∂torusMeasure d = 1 := by
  have h := integral_mollified_scaling η hm (fun y hy => hs y hy) hε hε1
  rw [hmass] at h
  exact h

end Mollifier

end BecknerOnofri.V2.Reaudit.Obstruction

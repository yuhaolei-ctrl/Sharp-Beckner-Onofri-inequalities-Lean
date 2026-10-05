module

public import BecknerOnofri.ConditionalExpectations
public import Legacy.BecknerOnofri.SmoothFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Integrating out future coordinates preserves rapid Fourier decay and hence
smoothness of the actual one-coordinate conditional density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Function
open scoped BigOperators ContDiff

namespace BecknerOnofri.HighDim.ConditionalEntropy
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open RadialWiener SmoothFourier

private theorem character_add {d : ℕ} (k : Frequency d) (x y : Torus d) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

def sectionCoefficients {d : ℕ} (a : Frequency d → ℂ) (i : Fin d)
    (x : Torus d) (k : Frequency d) : ℂ :=
  ∫ y : suffixCoordinates d (i.val + 1) → UnitAddCircle,
    a k * UnitAddTorus.mFourier k
      (updateFinset (Function.update x i 0) (suffixCoordinates d (i.val + 1)) y)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)

theorem sectionCoefficients_norm_le {d : ℕ} (a : Frequency d → ℂ)
    (i : Fin d) (x : Torus d) (k : Frequency d) :
    ‖sectionCoefficients a i x k‖ ≤ ‖a k‖ := by
  unfold sectionCoefficients
  calc
    _ ≤ ∫ y : suffixCoordinates d (i.val + 1) → UnitAddCircle,
        ‖a k * UnitAddTorus.mFourier k
          (updateFinset (Function.update x i 0) (suffixCoordinates d (i.val + 1)) y)‖
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := norm_integral_le_integral_norm _
    _ = ‖a k‖ := by simp only [norm_mul, mFourier_norm_apply, mul_one]; simp

theorem sectionCoefficients_radial {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (i : Fin d) (x : Torus d) :
    ∀ m : ℕ, RadialSummable (sectionCoefficients a i x) m := by
  intro m
  apply (ha m).of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
  intro k
  exact mul_le_mul_of_nonneg_left (sectionCoefficients_norm_le a i x k)
    ((radialWeight_isWeight m).nonneg k)

theorem prefix_section_series {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (f : Torus d → ℝ)
    (he : ∀ x, (f x : ℂ) = absoluteFourierSeries a x)
    (i : Fin d) (x : Torus d) (z : UnitAddCircle) :
    (prefixDensity f (i.val + 1) (Function.update x i z) : ℂ) =
      absoluteFourierSeries (sectionCoefficients a i x) (Pi.single i z) := by
  classical
  let S := suffixCoordinates d (i.val + 1)
  let μ : Measure (S → UnitAddCircle) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  let g : (S → UnitAddCircle) → Torus d := fun y => updateFinset (Function.update x i z) S y
  have hg : Continuous g := by
    apply continuous_pi
    intro j
    simp only [g, updateFinset]
    split_ifs <;> fun_prop
  have hI (k : Frequency d) : Integrable (fun y => a k * UnitAddTorus.mFourier k (g y)) μ :=
    (continuous_const.mul ((UnitAddTorus.mFourier k).continuous.comp hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun k => ∫ y, ‖a k * UnitAddTorus.mFourier k (g y)‖ ∂μ) := by
    simpa only [norm_mul, mFourier_norm_apply, mul_one, integral_const,
      probReal_univ, one_smul] using ha
  have hi : i ∉ S := by simp [S]
  have hgadd (y : S → UnitAddCircle) : g y =
      updateFinset (Function.update x i 0) S y + Pi.single i z := by
    funext j
    by_cases hj : j = i
    · subst j; simp [g, updateFinset, hi]
    · simp [g, updateFinset, hj, Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  calc
    _ = ∫ y, (f (g y) : ℂ) ∂μ := by
      exact (integral_complex_ofReal).symm
    _ = ∫ y, ∑' k, a k * UnitAddTorus.mFourier k (g y) ∂μ := by
      simp only [he, absoluteFourierSeries]
    _ = ∑' k, ∫ y, a k * UnitAddTorus.mFourier k (g y) ∂μ :=
      (integral_tsum_of_summable_integral_norm hI hs).symm
    _ = _ := by
      apply tsum_congr
      intro k
      simp_rw [hgadd, character_add, ← mul_assoc]
      exact integral_mul_const _ _

theorem conditional_density_contDiff {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (f : Torus d → ℝ)
    (he : ∀ x, (f x : ℂ) = absoluteFourierSeries a x)
    (i : Fin d) (x : Torus d) :
    ContDiff ℝ ∞ (fun t : ℝ => conditionalDensity f i x (t : UnitAddCircle)) := by
  have hs := (radialSummable_zero a).mp (ha 0)
  have h := series_contDiff (sectionCoefficients a i x) (sectionCoefficients_radial a ha i x)
  have hsingle : ContDiff ℝ ∞ (fun t : ℝ => (Pi.single i t : Fin d → ℝ)) := by
    apply contDiff_pi.mpr
    intro j
    by_cases hj : j = i
    · subst j; simp only [Pi.single_eq_same]; exact contDiff_id
    · simpa [Pi.single_eq_of_ne hj] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  have hr := (Complex.reCLM.contDiff.comp (h.comp hsingle)).div_const (prefixDensity f i.val x)
  convert! hr using 1
  funext t
  unfold conditionalDensity
  congr 1
  have hq : quotient (Pi.single i t) = Pi.single i (t : UnitAddCircle) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [quotient]
    · simp [quotient, Pi.single_eq_of_ne hj]
  change prefixDensity f (i.val + 1) (Function.update x i (t : UnitAddCircle)) =
    (absoluteFourierSeries (sectionCoefficients a i x) (quotient (Pi.single i t))).re
  rw [hq, ← prefix_section_series a hs f he]
  rfl

#print axioms conditional_density_contDiff
end BecknerOnofri.HighDim.ConditionalEntropy

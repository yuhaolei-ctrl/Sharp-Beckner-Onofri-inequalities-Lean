module

public import BecknerOnofri.ContinuousVariations
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Quantitative comparison of the actual normalized Gibbs density under a
bounded continuous perturbation. These estimates control the omitted
Fourier tail in the certified iteration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.GibbsPerturbation
open ContinuousGibbs

theorem mean_mono {d : ℕ} {f g : Space d} (h : ∀ x, f x ≤ g x) :
    mean d f ≤ mean d g := integral_mono (integrable d f) (integrable d g) h

theorem weightedMean_mono {d : ℕ} (u : Space d) {f g : Space d}
    (h : ∀ x, f x ≤ g x) : weightedMean u f ≤ weightedMean u g := by
  apply mean_mono
  intro x
  exact mul_le_mul_of_nonneg_left (h x) (normalized_pos u x).le

theorem weightedMean_nonneg {d : ℕ} (u : Space d) {f : Space d}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ weightedMean u f := by
  simpa only [map_zero] using weightedMean_mono u (f := 0) (g := f) h

theorem partition_perturbation_upper {d : ℕ} (u w : Space d) (δ : ℝ)
    (hw : ∀ x, w x ≤ δ) : partition (u+w) ≤ Real.exp δ * partition u := by
  calc
    _ ≤ mean d (Real.exp δ • exponential u) := by
      apply mean_mono
      intro x
      simp only [exponential_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        smul_eq_mul, Real.exp_add]
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hw x)) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
    _ = _ := by rw [map_smul]; rfl

theorem normalized_perturbation_lower {d : ℕ} (u w : Space d) (δ : ℝ)
    (hw : ∀ x, |w x| ≤ δ) (x : Torus d) :
    Real.exp (-2*δ) * normalized u x ≤ normalized (u+w) x := by
  have hZ := partition_perturbation_upper u w δ (fun x => (abs_le.mp (hw x)).2)
  have he : Real.exp (-δ) * Real.exp (u x) ≤ Real.exp ((u+w) x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -δ + u x ≤ u x + w x
    linarith [(abs_le.mp (hw x)).1]
  have hden := div_le_div_of_nonneg_left (Real.exp_pos ((u+w) x)).le
    (partition_pos (u+w)) hZ
  have hnum := div_le_div_of_nonneg_right he
    (mul_pos (Real.exp_pos δ) (partition_pos u)).le
  have hh := hnum.trans hden
  have hexp : Real.exp (-2*δ) = Real.exp (-δ) / Real.exp δ := by
    rw [← Real.exp_sub]
    congr 1
    ring
  convert! hh using 1 <;>
    simp only [normalized, ContinuousMap.smul_apply, smul_eq_mul, exponential_apply, hexp] <;> ring

/-- Multiplicative control of the deficit from the maximal observable value.
The perturbation need not be a trigonometric polynomial. -/
theorem expectation_exponential_update {d : ℕ} (u w f : Space d) (δ : ℝ)
    (hw : ∀ x, |w x| ≤ δ) (hf : ∀ x, f x ≤ 1) :
    weightedMean (u+w) f ≤ 1-(1-weightedMean u f)*Real.exp (-2*δ) := by
  have hh : Real.exp (-2*δ) * weightedMean u (1-f) ≤ weightedMean (u+w) (1-f) := by
    calc
      _ = mean d (Real.exp (-2*δ) • (normalized u*(1-f))) := by
        rw [map_smul]; rfl
      _ ≤ _ := by
        apply mean_mono
        intro x
        simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply,
          ContinuousMap.sub_apply, ContinuousMap.one_apply, smul_eq_mul]
        change Real.exp (-2*δ) * (normalized u x * (1-f x)) ≤ normalized (u+w) x * (1-f x)
        nlinarith [normalized_perturbation_lower u w δ hw x, hf x]
  rw [map_sub,map_sub,weightedMean_one,weightedMean_one] at hh
  linarith

/-- A bounded observable has variance at most the square of its pointwise bound. -/
theorem variance_le {d : ℕ} (u f : Space d) (c : ℝ)
    (hf : ∀ x, |f x| ≤ c) : gibbsVariance u f ≤ c^2 := by
  rw [gibbsVariance_eq]
  have hh : weightedMean u (f^2) ≤ c^2 := by
    calc
      _ ≤ weightedMean u (ContinuousMap.const (Torus d) (c^2)) := by
        apply weightedMean_mono
        intro x
        change (f x)^2 ≤ c^2
        nlinarith [(abs_le.mp (hf x)).1, (abs_le.mp (hf x)).2]
      _ = _ := weightedMean_const _ _
  nlinarith [sq_nonneg (weightedMean u f)]

theorem covariance_le {d : ℕ} (u f w : Space d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hf : ∀ x, |f x| ≤ 1) (hw : ∀ x, |w x| ≤ δ) :
    logPartitionHessian u f w ≤ δ := by
  by_cases hz : δ=0
  · have hwz : w=0 := by
      ext x
      exact abs_eq_zero.mp (le_antisymm ((hw x).trans_eq hz) (abs_nonneg _))
    simp [hwz,hz]
  have hp : 0<δ := lt_of_le_of_ne hδ (Ne.symm hz)
  have hvar := gibbsVariance_nonneg u (δ • f-w)
  have hfe := variance_le u f 1 hf
  have hwe := variance_le u w δ hw
  have hex : gibbsVariance u (δ • f-w) =
      δ^2*gibbsVariance u f+gibbsVariance u w-2*δ*logPartitionHessian u f w := by
    rw [← logPartitionHessian_diag, map_sub, map_smul]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      map_sub, map_smul, smul_eq_mul, logPartitionHessian_diag]
    rw [logPartitionHessian_symmetric u w f]
    ring
  rw [hex] at hvar
  have hh : 0 ≤ δ^2 := sq_nonneg δ
  nlinarith

theorem covariance_abs_le {d : ℕ} (u f w : Space d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hf : ∀ x, |f x| ≤ 1) (hw : ∀ x, |w x| ≤ δ) :
    |logPartitionHessian u f w| ≤ δ := by
  apply abs_le.mpr
  refine ⟨?_, covariance_le u f w δ hδ hf hw⟩
  have hh := covariance_le u f (-w) δ hδ hf (by simpa using hw)
  rw [map_neg] at hh
  linarith

theorem expectation_line_hasDerivAt {d : ℕ} (u w f : Space d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => weightedMean (u+t • w) f)
      (logPartitionHessian (u+t • w) w f) t := by
  have hp : HasDerivAt (fun t : ℝ => u+t • w) w t := by
    convert! ((hasDerivAt_id t).smul_const w).const_add u using 1 <;> simp
  have h : HasDerivAt (fun s : ℝ => weightedMean (u+s • w))
      (logPartitionHessian (u+t • w) w) t := by
    apply HasFDerivAt.comp_hasDerivAt t (f := fun s : ℝ => u+s • w) (l := @weightedMean d)
      (f' := w) (l' := logPartitionHessian (u+t • w))
    · convert! hasFDerivAt_weightedMean (u+t • w) using 1
    · convert! hp using 1
  apply HasFDerivAt.comp_hasDerivAt t
    (l := fun A : Space d →L[ℝ] ℝ => A f)
    (l' := ContinuousLinearMap.apply ℝ ℝ f)
    (f := fun s : ℝ => weightedMean (u+s • w))
    (f' := logPartitionHessian (u+t • w) w)
  · convert! (ContinuousLinearMap.apply ℝ ℝ f).hasFDerivAt using 1
  · convert! h using 1

/-- The sharp sup-norm perturbation bound follows from covariance bounded by one. -/
theorem expectation_additive_update {d : ℕ} (u w f : Space d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hw : ∀ x, |w x| ≤ δ) (hf : ∀ x, |f x| ≤ 1) :
    |weightedMean (u+w) f-weightedMean u f| ≤ δ := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (expectation_line_hasDerivAt u w f t).hasDerivWithinAt)
    (fun t _ => by
      rw [Real.norm_eq_abs, logPartitionHessian_symmetric]
      exact covariance_abs_le (u+t • w) f w δ hδ hf hw)
  simpa only [one_smul,zero_smul,add_zero,Real.norm_eq_abs] using hh

#print axioms expectation_additive_update
#print axioms expectation_exponential_update
#print axioms covariance_le
end BecknerOnofri.HighDim.GibbsPerturbation

module

public import BecknerOnofri.SpinPressureCurvature
public import BecknerOnofri.SpinReferenceDefinitions
public import BecknerOnofri.SpinFiniteGibbs
public import BecknerOnofri.SpinProductProbability
public import BecknerOnofri.JensenRemainder

@[expose] public section

/-!
# Reduction of the finite-state inequality to one scalar function

On the slice `𝓟_t`, Lemma 5.19 makes `F - (7/25) H(·|b)` convex. With the explicit reference
law `q(t)`, the Bregman identity for relative entropy and the Gibbs variational principle give
`G_t(p) ≥ 𝓑(t)` for every `p ∈ 𝓟_t` (manuscript, the paragraph "One explicit reference law"
before Lemma 5.20).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Set

namespace BecknerOnofri.HighDim.Spin

/-- Convexity of `F - (7/25) H(·|b)` on mean slices, in first-order form. -/
theorem fixed_mean_entropy_convexity_sharp {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j, 0 < p j) (hq : Feasible q) (hmean : mean p = mean q) :
    functional p + (∑ j : Count, gradient p j * (q j - p j)) +
      (7 / 25) * relativeEntropy q p ≤ functional q := by
  let v := q - p
  let f : ℝ → ℝ := fun t => functional (p + t • v) - (7 / 25) * relativeEntropy (p + t • v) reference
  let f' : ℝ → ℝ := fun t => functionalSlope p v t - (7 / 25) * entropySlope p v t
  let f'' : ℝ → ℝ := fun t => functionalHessian p v t - (7 / 25) * entropyHessian p v t
  have hv : (∑ j : Count, v j) = 0 := by
    simp [v, Finset.sum_sub_distrib, hp.2.1, hq.2.1]
  have hvx : mean v = 0 := by simp [v, mean_sub, hmean]
  have hcont : Continuous f := (functional_segment_continuous p v).sub
    ((relativeEntropy_reference_continuous.comp (by fun_prop)).const_mul _)
  have hd (t : ℝ) (ht : ∀ j, 0 < p j + t * v j) : HasDerivAt f (f' t) t :=
    (functional_segment_derivative p v t ht).sub
      ((entropy_segment_derivative p v t ht).const_mul _)
  have hdd (t : ℝ) (ht : ∀ j, 0 < p j + t * v j) : HasDerivAt f' (f'' t) t :=
    (functional_segment_second_derivative p v t ht).sub
      ((entropy_segment_second_derivative p v t ht).const_mul _)
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ f'' t := by
    have hr := feasible_segment hp hq ⟨ht.1.le, ht.2.le⟩
    have hrpos : ∀ j, 0 < (p + t • v) j := segment_positive hpos hq ht.1.le ht.2
    have hc := fixed_mean_curvature_sharp hr hrpos hv hvx
    change quadratic v ≤ (43 / 50) * entropyHessian p v t at hc
    dsimp [f'', functionalHessian]
    linarith
  have h := second_order_support hcont.continuousOn (hd 0 (by simpa using hpos))
    (fun t ht => hd t (segment_positive hpos hq ht.1.le ht.2))
    (fun t ht => hdd t (segment_positive hpos hq ht.1.le ht.2)) hb
  have he : p + (1 : ℝ) • v = q := by dsimp [v]; module
  simp only [f, f', zero_smul, add_zero, he, zero_div] at h
  have hB := entropy_bregman_identity hpos hp.2.1 hq.2.1
  have hG := slope_at_zero_eq_gradient p v hpos
  change functionalSlope p v 0 = (∑ j : Count, gradient p j * (q j - p j)) at hG
  change relativeEntropy q reference - relativeEntropy p reference - entropySlope p v 0 =
    relativeEntropy q p at hB
  linarith

/-! ### The reference law -/

theorem refShift_mem {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < refShift t ∧ refShift t < 1 := by
  unfold refShift
  have h4 : t ^ 5 ≤ t := by
    calc t ^ 5 ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
      _ = t := pow_one t
  have h5 : 0 < t ^ 5 := by positivity
  constructor <;> nlinarith

theorem refAtom_mem {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < refAtom t ∧ refAtom t < 1 := by
  unfold refAtom
  have h5 : 0 < t ^ 5 := by positivity
  have hd : 0 < 4 - 4 * t + t ^ 5 := by linarith
  refine ⟨div_pos h5 hd, (div_lt_one hd).mpr (by linarith)⟩

theorem refLaw_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) : 0 < refLaw t j := by
  obtain ⟨hz0, hz1⟩ := refShift_mem ht0 ht1
  obtain ⟨ha0, ha1⟩ := refAtom_mem ht0 ht1
  have hp := productProbability_pos (by linarith : -1 < refShift t) hz1 j
  unfold refLaw
  have : 0 < (1 - refAtom t) * productProbability (refShift t) j := mul_pos (by linarith) hp
  split_ifs <;> linarith

theorem refLaw_mass (t : ℝ) : (∑ j : Count, refLaw t j) = 1 := by
  unfold refLaw
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, productProbability_mass]
  simp

theorem refLaw_mean {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : mean (refLaw t) = t := by
  have hm := productProbability_mean (refShift t)
  unfold mean at hm ⊢
  unfold refLaw
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ j : Count, meanCoordinate j * ((1 - refAtom t) * productProbability (refShift t) j)) =
      (1 - refAtom t) * refShift t := by
    rw [← hm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [hm]; ring)
  have h2 : (∑ j : Count, meanCoordinate j * (if j = 12 then refAtom t else 0)) = refAtom t := by
    rw [Finset.sum_eq_single (12 : Count) (fun b _ hb => by simp [hb]) (by simp)]
    norm_num [meanCoordinate, meanCoordinateQ]
  rw [h1, h2]
  have hd : 4 - 4 * t + t ^ 5 ≠ 0 := by nlinarith [pow_nonneg ht0 5]
  have key : refAtom t * (1 - refShift t) = t ^ 5 / 4 := by
    unfold refAtom refShift
    rw [div_mul_eq_mul_div, div_eq_iff hd]
    ring
  have hz : refShift t = t - t ^ 5 / 4 := rfl
  linear_combination key + hz

theorem refLaw_feasible {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : FeasibleAt t (refLaw t) := by
  refine ⟨⟨fun j => (refLaw_pos ht0 ht1 j).le, refLaw_mass t, ?_⟩, refLaw_mean ht0.le ht1⟩
  obtain ⟨hz0, hz1⟩ := refShift_mem ht0 ht1
  obtain ⟨ha0, ha1⟩ := refAtom_mem ht0 ht1
  have hp0 := (productProbability_feasible hz0.le hz1.le).1.2.2
  have hn := productProbability_nonneg hz0.le hz1.le 0
  unfold refLaw
  simp only [show (0 : Count) ≠ 12 by decide, ite_false, add_zero]
  calc (1 - refAtom t) * productProbability (refShift t) 0 ≤ 1 * productProbability (refShift t) 0 :=
        mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ 1 / 4096 := by linarith

/-! ### The reduction `G_t(p) ≥ 𝓑(t)` -/

/-- For `0 < t < 1` and `p ∈ 𝓟_t`, `G_t(p) ≥ 𝓑(t)`. -/
theorem pressureScalar_le_penalized {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {p : Count → ℝ}
    (hp : FeasibleAt t p) : pressureScalar t ≤ penalized t p := by
  have hqf := refLaw_feasible ht0 ht1
  have hqpos := refLaw_pos ht0 ht1
  have hτ : 0 < refTau t := by
    have := eta_nonneg ht0.le ht1.le
    unfold refTau; linarith
  have heta := eta_nonneg ht0.le ht1.le
  -- convexity of `F - (7/25) H` and the Bregman identity for `H`
  have hconv := fixed_mean_entropy_convexity_sharp hqf.1 hqpos hp.1
    (by rw [hqf.2, hp.2])
  have hB := entropy_bregman_identity hqpos hqf.1.2.1 hp.1.2.1
  -- the shifted gradient `h_j = g_j - μ (x_j - t)`
  let h : Count → ℝ := fun j => refGradient t j - refMu t * (meanCoordinate j - t)
  have hgibbs := finite_gibbs_variational (refLaw t) p (fun j => -h j / refTau t) hqpos hp.1.1 hp.1.2.1
  have hlog (j : Count) : Real.log ((refLaw t) j / reference j) = Real.log ((refLaw t) j) - Real.log (reference j) :=
    Real.log_div (hqpos j).ne' (reference_pos j).ne'
  -- the linear terms combine into `∑ h_j (p_j - q_j)`
  have hpoint (j : Count) : gradient (refLaw t) j + eta t * (Real.log ((refLaw t) j) - Real.log (reference j) + 1) =
      h j + (2 + eta t) + refMu t * (meanCoordinate j - t) := by
    simp only [h, refGradient, gradient, interactionApply, hlog]
    ring
  have hmass : (∑ j : Count, (p j - (refLaw t) j)) = 0 := by
    rw [Finset.sum_sub_distrib, hp.1.2.1, hqf.1.2.1, sub_self]
  have hmeanz : (∑ j : Count, (meanCoordinate j - t) * (p j - (refLaw t) j)) = 0 := by
    have hmp := hp.2
    have hmq := hqf.2
    unfold mean at hmp hmq
    have : (∑ j : Count, (meanCoordinate j - t) * (p j - (refLaw t) j)) =
        (∑ j : Count, meanCoordinate j * p j) - (∑ j : Count, meanCoordinate j * (refLaw t) j) -
          t * (∑ j : Count, (p j - (refLaw t) j)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hmp, hmq, hmass]
    ring
  have hlin : (∑ j : Count, gradient (refLaw t) j * (p j - (refLaw t) j)) +
      eta t * entropySlope (refLaw t) (p - (refLaw t)) 0 = (∑ j : Count, h j * (p j - (refLaw t) j)) := by
    unfold entropySlope
    simp only [zero_mul, add_zero, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    have : ∀ j : Count, gradient (refLaw t) j * (p j - (refLaw t) j) +
        eta t * ((Real.log ((refLaw t) j) - Real.log (reference j) + 1) * (p j - (refLaw t) j)) =
        h j * (p j - (refLaw t) j) + (2 + eta t) * (p j - (refLaw t) j) +
          refMu t * ((meanCoordinate j - t) * (p j - (refLaw t) j)) := by
      intro j
      have := hpoint j
      linear_combination (p j - (refLaw t) j) * this
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hmass, hmeanz, mul_zero, add_zero]
  -- the constant terms
  have hqh : (∑ j : Count, (refLaw t) j * h j) =
      (2 + eta t) * relativeEntropy (refLaw t) reference - 2 * quadratic (refLaw t) := by
    have hz : (∑ j : Count, (refLaw t) j * (meanCoordinate j - t)) = 0 := by
      have hmq := hqf.2
      unfold mean at hmq
      have : (∑ j : Count, (refLaw t) j * (meanCoordinate j - t)) =
          (∑ j : Count, meanCoordinate j * (refLaw t) j) - t * (∑ j : Count, (refLaw t) j) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [this, hmq, hqf.1.2.1]; ring
    have hquad : (∑ j : Count, (refLaw t) j * interactionApply (refLaw t) j) =
        quadratic (refLaw t) := by
      simp only [interactionApply, quadratic, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    simp only [h, refGradient, relativeEntropy]
    have : ∀ j : Count, (refLaw t) j * ((2 + eta t) * Real.log ((refLaw t) j / reference j) -
        2 * interactionApply (refLaw t) j - refMu t * (meanCoordinate j - t)) =
        (2 + eta t) * ((refLaw t) j * Real.log ((refLaw t) j / reference j)) - 2 * ((refLaw t) j * interactionApply (refLaw t) j) -
          refMu t * ((refLaw t) j * (meanCoordinate j - t)) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hz, hquad, mul_zero, sub_zero]
  -- the Gibbs step
  have hsum : (∑ j : Count, p j * (-h j / refTau t)) =
      -(∑ j : Count, p j * h j) / refTau t := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum] at hgibbs
  have hZ : (∑ j : Count, (refLaw t) j * Real.exp (-h j / refTau t)) =
      ∑ j : Count, refLaw t j *
        Real.exp ((-refGradient t j + refMu t * (meanCoordinate j - t)) / refTau t) := by
    exact Finset.sum_congr rfl (fun j _ => by simp only [h]; congr 2; ring)
  rw [hZ] at hgibbs
  have hpl : (∑ j : Count, p j * h j) - (∑ j : Count, (refLaw t) j * h j) =
      ∑ j : Count, h j * (p j - (refLaw t) j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hgt := (div_le_iff₀ hτ).mp (by linarith : -(∑ j : Count, p j * h j) / refTau t ≤
    Real.log (∑ j : Count, refLaw t j *
      Real.exp ((-refGradient t j + refMu t * (meanCoordinate j - t)) / refTau t)) +
        relativeEntropy p (refLaw t))
  unfold pressureScalar penalized functional at *
  unfold refTau at hgt ⊢
  nlinarith [hconv, hB, hlin, hqh, hpl, hgt, mul_nonneg heta (le_refl (0 : ℝ))]

end BecknerOnofri.HighDim.Spin

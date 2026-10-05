import BecknerOnofri.SpinConditionalMean
import BecknerOnofri.SpinBinaryJensen
import BecknerOnofri.BesselIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! The binary entropy contraction for each actual earlier-spin likelihood,
including positivity of its normalizing probability. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BecknerOnofri.HighDim.Spin
open EntropyShearer ConditionalEntropy

theorem prefixLikelihood_integral (k : ℕ) (σ : Configuration) :
    (∫ x, prefixLikelihood k σ x ∂torusMeasure 12) =
      ∏ j : Fin 12, if j.val < k then (1 / 2 : ℝ) else 1 := by
  have hcos : (∫ z : UnitAddCircle, (fourier 1 z).re ∂AddCircle.haarAddCircle) = 0 := by
    have hi := (map_continuous (fourier (1 : ℤ) : C(UnitAddCircle, ℂ))).integrable_of_hasCompactSupport
      (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
    have h := integral_re hi
    change (∫ z : UnitAddCircle, (fourier 1 z).re ∂AddCircle.haarAddCircle) =
      (∫ z : UnitAddCircle, fourier 1 z ∂AddCircle.haarAddCircle).re at h
    rw [circle_fourier_integral] at h
    norm_num at h
    simpa using h
  have hir : Integrable (fun z : UnitAddCircle => (fourier 1 z).re)
      AddCircle.haarAddCircle :=
    (Complex.continuous_re.comp (map_continuous (fourier (1 : ℤ)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [prefixLikelihood, Finset.prod_filter, torusCosines, torusMeasure]
  rw [integral_fintype_prod_eq_prod (fun j : Fin 12 => fun z : UnitAddCircle =>
    if j.val < k then
      (if j ∈ σ then (1 + (fourier 1 z).re) / 2 else (1 - (fourier 1 z).re) / 2) else 1)]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hk : j.val < k
  · simp only [hk, ite_true]
    by_cases hσ : j ∈ σ
    · simp only [hσ, ite_true, integral_div]
      rw [integral_add (integrable_const 1) hir, hcos]
      simp
    · simp only [hσ, ite_false, integral_div]
      rw [integral_sub (integrable_const 1) hir, hcos]
      simp
  · simp [hk]

theorem prefixLikelihood_integral_pos (k : ℕ) (σ : Configuration) :
    0 < ∫ x, prefixLikelihood k σ x ∂torusMeasure 12 := by
  rw [prefixLikelihood_integral]
  apply Finset.prod_pos
  intro j hj
  split_ifs <;> norm_num

theorem prefix_mass_pos {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (k : ℕ) (σ : Configuration) :
    0 < ∫ x, f x * prefixLikelihood k σ x ∂torusMeasure 12 := by
  have hfb := hf.bounded
  obtain ⟨_, c, B, hc, hbounds⟩ := hf
  have hi := (prefixLikelihood_bounded k σ).integrable
  have h := integral_mono (hi.const_mul c) (hfb.mul (prefixLikelihood_bounded k σ)).integrable
    (fun x => mul_le_mul_of_nonneg_right (hbounds x).1 (prefixLikelihood_bounds k σ x).1)
  rw [integral_const_mul] at h
  exact (mul_pos hc (prefixLikelihood_integral_pos k σ)).trans_le h

theorem posterior_binary_entropy {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (i : Fin 12) (σ : Configuration) :
    let m := ∫ x, f x * prefixLikelihood i.val σ x ∂torusMeasure 12
    0 < m ∧ m * binaryCost
      ((∫ x, f x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12) / m) ≤
      ∫ x, f x * (prefixLikelihood i.val σ x * binaryCost (conditionalCosineMoment f i 1 x))
        ∂torusMeasure 12 := by
  dsimp only
  let m := ∫ x, f x * prefixLikelihood i.val σ x ∂torusMeasure 12
  let q : Torus 12 → ℝ := fun x => (f x * prefixLikelihood i.val σ x) / m
  have hm : 0 < m := prefix_mass_pos hf i.val σ
  refine ⟨hm, ?_⟩
  have hq : BoundedMeasurable q := by
    simpa only [q, div_eq_mul_inv] using
      (hf.bounded.mul (prefixLikelihood_bounded i.val σ)).mul (BoundedMeasurable.const m⁻¹)
  have hqpos (x : Torus 12) : 0 ≤ q x :=
    div_nonneg (mul_nonneg (hf.pos x).le (prefixLikelihood_bounds i.val σ x).1) hm.le
  have hqm : (∫ x, q x ∂torusMeasure 12) = 1 := by
    change (∫ x, (f x * prefixLikelihood i.val σ x) / m ∂torusMeasure 12) = 1
    rw [integral_div]
    exact div_self hm.ne'
  have h := binaryCost_weighted_jensen hq hqpos hqm
    (conditional_moment_bounded hf i 1) (conditional_moment_abs_le_one hf i 1)
  have he (g : Torus 12 → ℝ) :
      (∫ x, q x * g x ∂torusMeasure 12) =
        (∫ x, f x * (prefixLikelihood i.val σ x * g x) ∂torusMeasure 12) / m := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [q]
    ring
  rw [he, he, ← conditional_spin_mean hf i σ] at h
  simpa only [mul_comm] using (le_div_iff₀ hm).mp h

#print axioms posterior_binary_entropy

end BecknerOnofri.HighDim.Spin

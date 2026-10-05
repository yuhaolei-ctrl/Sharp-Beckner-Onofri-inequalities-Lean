import Legacy.TorusEndpoint.EndpointNormalization
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Square summability of the actual critical Green multiplier

The frequency radius is the Euclidean radius from EndpointNormalization,
not the function-space supremum norm. Lattice summability is proved by a
finite product comparison; it is not an additional hypothesis.
-/

open Filter
open MeasureTheory
open scoped BigOperators ENNReal

namespace Legacy.TorusEndpoint.GreenMultiplierSummability

set_option maxHeartbeats 800000

noncomputable def radiusSq {d : ℕ} (k : Frequency d) : ℝ :=
  ∑ j : Fin d, (k j : ℝ) ^ 2

lemma radiusSq_nonneg {d : ℕ} (k : Frequency d) : 0 ≤ radiusSq k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma radiusSq_one_le {d : ℕ} {k : Frequency d} (hk : k ≠ 0) :
    1 ≤ radiusSq k := by
  classical
  have hn : ∃ j : Fin d, k j ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  obtain ⟨j, hj⟩ := hn
  have hsqZ : (1 : ℤ) ≤ (k j) ^ 2 := by
    have hp := sq_pos_of_ne_zero hj
    omega
  have hsq : (1 : ℝ) ≤ (k j : ℝ) ^ 2 := by exact_mod_cast hsqZ
  exact hsq.trans (Finset.single_le_sum (fun i _ => sq_nonneg (k i : ℝ))
    (Finset.mem_univ j))

lemma frequencyRadius_sq {d : ℕ} (k : Frequency d) :
    frequencyRadius k ^ 2 = radiusSq k :=
  Real.sq_sqrt (radiusSq_nonneg k)

lemma summable_int_one_add_sq_inv :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply hbase.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hp : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)), ← one_div]
  exact one_div_le_one_div_of_le hp (by linarith)

noncomputable def productMajorant {d : ℕ} (k : Frequency d) : ℝ :=
  ∏ j : Fin d, (1 + (k j : ℝ) ^ 2)⁻¹

lemma productMajorant_nonneg {d : ℕ} (k : Frequency d) :
    0 ≤ productMajorant k := by
  apply Finset.prod_nonneg
  intro j _
  positivity

lemma summable_productMajorant (d : ℕ) :
    Summable (productMajorant : Frequency d → ℝ) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    have hp := summable_int_one_add_sq_inv.mul_of_nonneg ih
      (fun n => by positivity) (fun k => productMajorant_nonneg k)
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff.mp
    simpa [Function.comp_def, productMajorant, Fin.prod_univ_succ, Fin.consEquiv, mul_comm] using hp

lemma shifted_radial_inv_le_product {d : ℕ} (k : Frequency d) :
    (1 + radiusSq k)⁻¹ ^ d ≤ productMajorant k := by
  have hprod : (∏ j : Fin d, (1 + (k j : ℝ) ^ 2)) ≤ (1 + radiusSq k) ^ d := by
    calc
      _ ≤ ∏ _ : Fin d, (1 + radiusSq k) := by
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          simpa [radiusSq, add_comm] using add_le_add_left
            (Finset.single_le_sum (fun i _ => sq_nonneg (k i : ℝ)) (Finset.mem_univ j)) 1
      _ = _ := by simp
  have hpos : 0 < ∏ j : Fin d, (1 + (k j : ℝ) ^ 2) := by
    apply Finset.prod_pos
    intro j _
    positivity
  simpa only [productMajorant, ← Finset.prod_inv_distrib, ← inv_pow] using
    inv_anti₀ hpos hprod

lemma radial_inv_le_product {d : ℕ} {k : Frequency d} (hk : k ≠ 0) :
    (radiusSq k)⁻¹ ^ d ≤ (2 : ℝ) ^ d * productMajorant k := by
  have hr := radiusSq_one_le hk
  have hp : 0 < radiusSq k := lt_of_lt_of_le (by norm_num) hr
  have hshift : 0 < 1 + radiusSq k := by positivity
  have hpow : (1 + radiusSq k) ^ d ≤ (2 : ℝ) ^ d * radiusSq k ^ d := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + radiusSq k)
        (by linarith : 1 + radiusSq k ≤ 2 * radiusSq k) d
  have hdiv : 1 / radiusSq k ^ d ≤ (2 : ℝ) ^ d / (1 + radiusSq k) ^ d := by
    apply (div_le_div_iff₀ (pow_pos hp d) (pow_pos hshift d)).mpr
    simpa only [one_mul] using hpow
  calc
    _ = 1 / radiusSq k ^ d := by simp
    _ ≤ (2 : ℝ) ^ d / (1 + radiusSq k) ^ d := hdiv
    _ = (2 : ℝ) ^ d * ((1 + radiusSq k)⁻¹ ^ d) := by simp [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (shifted_radial_inv_le_product k) (by positivity)

lemma summable_nonzero_radial_inverse (d : ℕ) :
    Summable (fun k : Frequency d => if k = 0 then 0 else (radiusSq k)⁻¹ ^ d) := by
  apply Summable.of_nonneg_of_le _ _ ((summable_productMajorant d).mul_left ((2 : ℝ) ^ d))
  · intro k
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (inv_nonneg.mpr (radiusSq_nonneg k)) d
  · intro k
    split_ifs with hk
    · exact mul_nonneg (by positivity) (productMajorant_nonneg k)
    · exact radial_inv_le_product hk

/-- The actual normalized Green multiplier with zero mean. -/
noncomputable def greenMultiplier (d : ℕ) (k : Frequency d) : ℝ :=
  if k = 0 then 0 else 1 / (endpointSigma d * frequencyRadius k ^ d)

@[simp] lemma greenMultiplier_zero (d : ℕ) : greenMultiplier d 0 = 0 := by
  simp [greenMultiplier]

lemma greenMultiplier_of_ne_zero {d : ℕ} {k : Frequency d} (hk : k ≠ 0) :
    greenMultiplier d k = 1 / (endpointSigma d * frequencyRadius k ^ d) := by
  simp [greenMultiplier, hk]

lemma greenMultiplier_sq (d : ℕ) (k : Frequency d) :
    greenMultiplier d k ^ 2 = (endpointSigma d)⁻¹ ^ 2 *
      (if k = 0 then 0 else (radiusSq k)⁻¹ ^ d) := by
  by_cases hk : k = 0
  · simp [greenMultiplier, hk]
  · have hp : (frequencyRadius k ^ d) ^ 2 = (radiusSq k) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul, frequencyRadius_sq]
    simp only [greenMultiplier, if_neg hk, div_pow, one_pow, mul_pow]
    rw [hp]
    simp [div_eq_mul_inv, mul_comm]

theorem summable_greenMultiplier_sq (d : ℕ) :
    Summable (fun k : Frequency d => greenMultiplier d k ^ 2) := by
  exact ((summable_nonzero_radial_inverse d).mul_left ((endpointSigma d)⁻¹ ^ 2)).congr
    (fun k => (greenMultiplier_sq d k).symm)

@[simp] lemma greenMultiplier_neg (d : ℕ) (k : Frequency d) :
    greenMultiplier d (-k) = greenMultiplier d k := by
  simp [greenMultiplier]

lemma greenMultiplier_pos {d : ℕ} (hd : 0 < d)
    {k : Frequency d} (hk : k ≠ 0) : 0 < greenMultiplier d k := by
  rw [greenMultiplier_of_ne_zero hk]
  exact one_div_pos.mpr (mul_pos (endpointSigma_pos hd)
    (pow_pos (frequencyRadius_pos hk) d))

/-- The proved multiplier sequence as an actual square-summable complex vector. -/
noncomputable def greenCoefficients (d : ℕ) : lp (fun _ : Frequency d => ℂ) 2 :=
  ⟨fun k => (greenMultiplier d k : ℂ), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] using summable_greenMultiplier_sq d⟩

/-- An actual Haar L² function, constructed through the genuine Fourier Hilbert basis.
No choice of a pointwise logarithmic representative is asserted. -/
noncomputable def greenL2 (d : ℕ) : Lp ℂ 2 (torusMeasure d) :=
  (UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm (greenCoefficients d)

theorem greenL2_integrable (d : ℕ) : Integrable (greenL2 d) (torusMeasure d) :=
  MemLp.integrable (by norm_num) (Lp.memLp (greenL2 d))

theorem greenL2_fourierCoeff (d : ℕ) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (greenL2 d) k = (greenMultiplier d k : ℂ) := by
  calc
    _ = UnitAddTorus.mFourierBasis.repr (greenL2 d) k :=
      (UnitAddTorus.mFourierBasis_repr (greenL2 d) k).symm
    _ = _ := by simp [greenL2, greenCoefficients]

theorem hasSum_greenL2 (d : ℕ) :
    HasSum (fun k : Frequency d => (greenMultiplier d k : ℂ) •
      UnitAddTorus.mFourierLp 2 k) (greenL2 d) := by
  apply (UnitAddTorus.hasSum_mFourier_series_L2 (greenL2 d)).congr_fun
  intro k
  exact congrArg (fun c : ℂ => c • UnitAddTorus.mFourierLp 2 k)
    (greenL2_fourierCoeff d k).symm

theorem greenL2_integral_zero (d : ℕ) :
    (∫ x, greenL2 d x ∂torusMeasure d) = 0 := by
  simpa only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul, greenMultiplier_zero, Complex.ofReal_zero, torusMeasure]
    using greenL2_fourierCoeff d 0

end Legacy.TorusEndpoint.GreenMultiplierSummability

#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.summable_int_one_add_sq_inv
#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.summable_productMajorant
#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.radial_inv_le_product
#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.summable_greenMultiplier_sq
#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.greenL2_fourierCoeff
#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.hasSum_greenL2
#print axioms Legacy.TorusEndpoint.GreenMultiplierSummability.greenL2_integral_zero

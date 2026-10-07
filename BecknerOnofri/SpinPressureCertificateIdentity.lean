module

public import BecknerOnofri.SpinPressureCertificateEnclosure
public import BecknerOnofri.SpinReferenceDefinitions
public import BecknerOnofri.SpinAlgebra
public import BecknerOnofri.SpinProductMoments

@[expose] public section

/-!
# The enclosed expression is `𝓑(t) - t⁴/200`

Lemma 5.20 (lem:section5-scalar-pressure). For `0 < t < 1` the real expression evaluated by
the certificate equals `pressureScalar t - t⁴/200`: the moments of the reference law are
`m_s = (1-a) zˢ + a` (eq:section5-spin-reference), `(Wq)_j = ∑ w_s A_{s,j} m_s`, and the
pressure sum takes the cancelled form eq:12-pressure-cancellation.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

open Real Finset

/-- The rational number of a pair. -/
def ratQ (p : RatPair) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

theorem ratVal_eq (p : RatPair) : ratVal p = ((ratQ p : ℚ) : ℝ) := by
  simp [ratVal, ratQ]

/-! The two identities involving `w_s` are proved by `norm_num` case by case rather than by
kernel evaluation: the NanoDa kernel is very slow on some of these rational normalizations. -/

theorem weightData_eq : ∀ i : Order, ratQ (weightData.getD i (0, 1)) = weightQ i := by
  intro i
  fin_cases i <;> norm_num [ratQ, weightData, weightQ, Nat.choose]

theorem referenceData_eq : ∀ j : Count, ratQ (referenceData.getD j (0, 1)) = referenceQ j := by
  decide +kernel

theorem coordinateData_eq :
    ∀ j : Count, ratQ (coordinateData.getD j (0, 1)) = meanCoordinateQ j := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem weightedMomentData_eq : ∀ j : Count, ∀ i : Order,
    ratQ ((weightedMomentData.getD j []).getD i (0, 1)) = weightQ i * momentQ i j := by
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [ratQ, weightedMomentData, weightQ, momentQ, Finset.sum_range_succ, Nat.choose]

theorem momentQ_last : ∀ i : Order, momentQ i 12 = 1 := by decide +kernel

theorem zR_eq (t : ℝ) : zR t = refShift t := by simp only [zR, refShift]; ring

section

variable {t : ℝ}

theorem ppR_pos (ht1 : t < 1) : 0 < ppR t := by simp only [ppR]; linarith

theorem denR_pos (ht0 : 0 < t) (ht1 : t < 1) : 0 < denR t := by
  simp only [denR]; have := ppR_pos ht1; positivity

theorem refAtom_eq : refAtom t = t ^ 5 / denR t := by simp only [refAtom, denR, ppR]

theorem one_sub_refAtom (ht0 : 0 < t) (ht1 : t < 1) : 1 - refAtom t = ppR t / denR t := by
  have := denR_pos ht0 ht1
  rw [refAtom_eq]
  field_simp
  simp only [denR]; ring

theorem zR_pos (ht0 : 0 < t) (ht1 : t < 1) : 0 < zR t ∧ zR t < 1 := by
  have h5 : t ^ 5 ≤ t := pow_le_of_le_one ht0.le ht1.le (by norm_num)
  have h5' : 0 < t ^ 5 := by positivity
  simp only [zR]
  constructor <;> linarith

theorem refLaw_pos' (ht0 : 0 < t) (ht1 : t < 1) (j : Count) : 0 < refLaw t j := by
  have ha : 0 < 1 - refAtom t := by
    rw [one_sub_refAtom ht0 ht1]; exact div_pos (ppR_pos ht1) (denR_pos ht0 ht1)
  have hz := zR_pos ht0 ht1
  rw [zR_eq] at hz
  have hp := productProbability_pos (t := refShift t) (by linarith) hz.2 j
  have hat : 0 ≤ refAtom t := by
    rw [refAtom_eq]; exact div_nonneg (by positivity) (denR_pos ht0 ht1).le
  unfold refLaw
  have : 0 ≤ (if j = 12 then refAtom t else 0) := by split_ifs <;> simp [hat]
  have := mul_pos ha hp
  linarith

/-- The moments of the reference law. -/
theorem refLaw_moment (ht0 : 0 < t) (ht1 : t < 1) (i : Order) :
    (∑ j : Count, moment i j * refLaw t j) = momR t i := by
  have hden := denR_pos ht0 ht1
  have h1 : (∑ j : Count, moment i j * refLaw t j) =
      (1 - refAtom t) * (∑ j : Count, moment i j * productProbability (refShift t) j) +
        refAtom t * moment i 12 := by
    simp only [refLaw, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [mul_ite, mul_comm]
  have hm : moment i 12 = 1 := by simp [moment, momentQ_last]
  rw [h1, productProbability_moment, hm, one_sub_refAtom ht0 ht1, refAtom_eq, ← zR_eq]
  simp only [momR]
  field_simp

theorem energyR_eq (ht0 : 0 < t) (ht1 : t < 1) : energyR t = quadratic (refLaw t) := by
  rw [quadratic_eq_sum, energyR, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [refLaw_moment ht0 ht1, ratVal_eq, weightData_eq]
  simp [weight, pow_two]

theorem linR_eq (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    linR t (weightedMomentData.getD j []) = interactionApply (refLaw t) j := by
  have h : interactionApply (refLaw t) j =
      ∑ i : Order, weight i * moment i j * (∑ k : Count, moment i k * refLaw t k) := by
    simp only [interactionApply, interaction_eq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, linR, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [refLaw_moment ht0 ht1, ratVal_eq, weightedMomentData_eq]
  simp [weight, moment]

theorem logRatioR_eq (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    logRatioR t j = Real.log (refLaw t j / reference j) := by
  have hden := denR_pos ht0 ht1
  have hpp := ppR_pos ht1
  have hz := zR_pos ht0 ht1
  have hb := reference_pos j
  by_cases hj : (j : ℕ) < 12
  · have hj12 : j ≠ 12 := by
      intro h; rw [h] at hj; exact absurd hj (by decide)
    rw [logRatioR, ite_eq_left_of_eq_true _ _ (eq_true hj)]
    have hratio : refLaw t j / reference j =
        ppR t / denR t * ((1 + zR t) ^ (j : ℕ) * (1 - zR t) ^ (12 - (j : ℕ))) := by
      rw [← one_sub_refAtom ht0 ht1, zR_eq]
      simp only [refLaw, hj12, ite_false, add_zero, productProbability]
      field_simp
    have h1 : 0 < 1 + zR t := by linarith
    have h2 : 0 < 1 - zR t := by linarith
    rw [hratio, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_div hpp.ne' hden.ne',
      Real.log_pow, Real.log_pow, Nat.cast_sub hj.le]
    push_cast
    ring
  · have hj12 : j = 12 := by
      have h12 : ((12 : Count) : ℕ) = 12 := rfl
      exact Fin.ext (by omega)
    subst hj12
    rw [logRatioR, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ ((12 : Count) : ℕ) < 12 by decide))]
    have hnum : 0 < ppR t * (1 + zR t) ^ 12 + 4096 * t ^ 5 := by
      have : 0 < 1 + zR t := by linarith
      positivity
    have hratio : refLaw t 12 / reference 12 =
        (ppR t * (1 + zR t) ^ 12 + 4096 * t ^ 5) / denR t := by
      have hr : reference 12 = 1 / 4096 := by simp [reference, referenceQ]
      rw [hr]
      simp only [refLaw, ite_true, productProbability, hr]
      rw [one_sub_refAtom ht0 ht1, refAtom_eq, zR_eq]
      rw [show ((12 : Count) : ℕ) = 12 from rfl]
      field_simp
      ring
    rw [hratio, Real.log_div hnum.ne' hden.ne']

theorem etaR_eq : etaR t = eta t := by
  simp only [etaR, eta, halfR, div_eq_mul_inv]
  try ring_nf

theorem eta_nonneg (ht0 : 0 < t) (ht1 : t < 1) : 0 ≤ eta t := by
  unfold eta
  have h1 : 0 < 1 - t ^ 2 := by nlinarith
  have h2 : 0 < 1 - t ^ 2 / 2 := by nlinarith
  positivity

theorem tauR_eq : tauR t = refTau t := by simp only [tauR, refTau, etaR_eq]

theorem muR_eq (ht1 : t < 1) (ht0 : 0 < t) : muR t = refMu t := by
  have h2 : (2 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - 1 / 2 * t ^ 2 ≠ 0 := by nlinarith
  simp only [muR, refMu, halfR]
  field_simp
  try ring

theorem termR_eq (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    termR t j = refLaw t j *
      Real.exp ((-refGradient t j + refMu t * (meanCoordinate j - t)) / refTau t) := by
  have hq := refLaw_pos' ht0 ht1 j
  have hb := reference_pos j
  have hτ : 0 < refTau t := by
    unfold refTau; linarith [eta_nonneg ht0 ht1]
  have hlaw : refLaw t j = reference j * Real.exp (Real.log (refLaw t j / reference j)) := by
    rw [Real.exp_log (div_pos hq hb)]; field_simp
  simp only [termR]
  rw [ratVal_eq, referenceData_eq, ratVal_eq, coordinateData_eq, logRatioR_eq ht0 ht1,
    linR_eq ht0 ht1, muR_eq ht1 ht0, tauR_eq]
  conv_rhs => rw [hlaw]
  rw [mul_assoc, ← Real.exp_add]
  simp only [reference, meanCoordinate, refGradient, refTau] at hτ ⊢
  have hτ' : (7 : ℝ) / 25 + eta t ≠ 0 := hτ.ne'
  have hτ'' : (7 : ℝ) + eta t * 25 ≠ 0 := by intro h; apply hτ'; linarith
  congr 2
  field_simp
  have hX := mul_inv_cancel₀ hτ''
  simp only [div_eq_mul_inv] at *
  linear_combination (Real.log (refLaw t j * ((referenceQ j : ℝ))⁻¹)) * hX

theorem pressureR_eq (ht0 : 0 < t) (ht1 : t < 1) :
    pressureR t = ∑ j : Count, refLaw t j *
      Real.exp ((-refGradient t j + refMu t * (meanCoordinate j - t)) / refTau t) := by
  rw [pressureR, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => termR_eq ht0 ht1 j

/-- The certificate's real expression is `𝓑(t) - t⁴/200`. -/
theorem scalarValue_eq (ht0 : 0 < t) (ht1 : t < 1) :
    scalarValue t = pressureScalar t - t ^ 4 / 200 := by
  rw [scalarValue, pressureScalar, energyR_eq ht0 ht1, pressureR_eq ht0 ht1, etaR_eq, tauR_eq]
  simp only [psi, binaryCost]
  ring

end

end BecknerOnofri.HighDim.Spin.PressureCertificate

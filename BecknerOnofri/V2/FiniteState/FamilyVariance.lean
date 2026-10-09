module

public import BecknerOnofri.V2.FiniteState.FamilyFeasible

@[expose] public section

/-!
# Explicit family: the spin-variance formula `d12-spin-eq:variance-x` (obligation U18)

CROSS-CHECK ROUTE.  The manuscript conditions on `θ` and uses the conditional variance
`(1-a²)/(χ+1)` of the spin bias plus a between-component term; that route is `FamilyBeta`
(`famNu_second_moment_beta`, `famSpinVar_eq_formula_beta`).  Here, independently, the second moment of the
beta-binomial component is computed from the finite Vandermonde identities of `FamilyFeasible`
(`E j = 12α/χ`, `E j(j-1) = 132 α(α+1)/(χ(χ+1))`) and the identity is closed algebraically.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Second moment of the spin average under the beta-binomial component:
`E_ν x² = a² + (1-a²)(χ+12)/(12(χ+1))`. -/
theorem famNu_second_moment {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ j : Count, meanCoordinate j ^ 2 * famNu t j =
      famBias t ^ 2 + (1 - famBias t ^ 2) * (famChi t + 12) / (12 * (famChi t + 1)) := by
  have hα := famAlpha_pos ht0 ht1
  have hβ := famBeta_pos ht0 ht1
  have hχ := famChi_pos ht0 ht1
  have h2 := betaBinom_second hα hβ
  have h1 := betaBinom_first hα hβ
  have h0 := betaBinom_sum hα hβ
  have e : ∀ j : Count, meanCoordinate j ^ 2 * famNu t j =
      (1 / 36) * ((j.val : ℝ) * ((j.val : ℝ) - 1) * betaBinom (famAlpha t) (famBeta t) j.val) -
      (11 / 36) * ((j.val : ℝ) * betaBinom (famAlpha t) (famBeta t) j.val) +
        betaBinom (famAlpha t) (famBeta t) j.val := by
    intro j
    rw [famNu_eq_betaBinom ht0 ht1, meanCoordinate_eq_real]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun j => (j : ℝ) * ((j : ℝ) - 1) * betaBinom (famAlpha t) (famBeta t) j) 13,
    Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) * betaBinom (famAlpha t) (famBeta t) j) 13,
    Fin.sum_univ_eq_sum_range (fun j => betaBinom (famAlpha t) (famBeta t) j) 13, h2, h1, h0,
    famAlpha_add_famBeta]
  unfold famAlpha
  have hχ1 : 0 < famChi t + 1 := by linarith
  field_simp
  ring

theorem regVar_eq_second_moment {p x : Count → ℝ} {t : ℝ} (hmass : ∑ j, p j = 1)
    (hmean : ∑ j, p j * x j = t) :
    regVar p x t = ∑ j, p j * x j ^ 2 - t ^ 2 := by
  have e : ∀ j, p j * (x j - t) ^ 2 = p j * x j ^ 2 - 2 * t * (p j * x j) + t ^ 2 * p j := by
    intro j; ring
  unfold regVar
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hmass,
    hmean]
  ring

/-- Route-independent core of `d12-spin-eq:variance-x`: given mass one, mean `t` and the second
moment of the component `ν`, the spin variance of `p(t)` is the closed formula. -/
theorem famSpinVar_eq_formula_of_moments {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hmass : ∑ j : Count, famLaw t j = 1) (hmean' : mean (famLaw t) = t)
    (hnu2 : ∑ j : Count, meanCoordinate j ^ 2 * famNu t j =
      famBias t ^ 2 + (1 - famBias t ^ 2) * (famChi t + 12) / (12 * (famChi t + 1))) :
    famSpinVar t = famVarFormula t := by
  have hχ := famChi_pos ht0 ht1
  have hω : famOmega t = (famChi t)⁻¹ := by
    have := famOmega_mul_famChi ht0 ht1
    field_simp
    linarith
  have hmean : ∑ j : Count, famLaw t j * meanCoordinate j = t := by
    simpa [mean, mul_comm] using hmean'
  have hx12 : ∀ j : Count, j.val = 12 → meanCoordinate j ^ 2 = 1 := by
    intro j hj; rw [meanCoordinate_eq_real, hj]; norm_num
  have e : ∀ j : Count, famLaw t j * meanCoordinate j ^ 2 =
      (1 - famLam t) * (meanCoordinate j ^ 2 * famNu t j) +
        famLam t * (if j.val = 12 then (1 : ℝ) else 0) := by
    intro j
    unfold famLaw
    by_cases hj : j.val = 12
    · simp [hj, hx12 j hj]
    · simp [hj]
      ring
  have hsm : ∑ j : Count, famLaw t j * meanCoordinate j ^ 2 =
      (1 - famLam t) * (famBias t ^ 2 + (1 - famBias t ^ 2) * (famChi t + 12) /
        (12 * (famChi t + 1))) + famLam t := by
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnu2,
      indicator_twelve_sum]
    ring
  unfold famSpinVar
  rw [regVar_eq_second_moment hmass hmean, hsm]
  have hb := famLam_bias ht0.le
  unfold famVarFormula
  rw [hω]
  have hχ1 : 0 < famChi t + 1 := by linarith
  have ht2 : t ^ 2 = ((1 - famLam t) * famBias t + famLam t) ^ 2 := by rw [hb]
  rw [ht2]
  field_simp
  ring

/-- The spin variance of the reference law equals the positive closed formula
`d12-spin-eq:variance-x` for `0 < t < 1`. -/
theorem famSpinVar_eq_formula {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famSpinVar t = famVarFormula t :=
  famSpinVar_eq_formula_of_moments ht0 ht1 (famLaw_sum ht0 ht1) (famLaw_mean ht0 ht1)
    (famNu_second_moment ht0 ht1)

theorem famVarFormula_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famVarFormula t := by
  have hχ := famChi_pos ht0 ht1
  have hω : famOmega t = (famChi t)⁻¹ := by
    have := famOmega_mul_famChi ht0 ht1
    field_simp
    linarith
  have h1 := famLam_lt_one ht0.le
  have h2 := famLam_nonneg ht0.le
  have ha0 := famBias_pos ht0 ht1
  have ha1 := famBias_lt_one ht0 ht1
  unfold famVarFormula
  rw [hω]
  have h3 : 0 < 1 - famLam t := by linarith
  have h4 : 0 < 1 - famBias t ^ 2 := by nlinarith
  have h5 : 0 < 1 - famBias t := by linarith
  have : 0 ≤ famLam t * (1 - famLam t) * (1 - famBias t) ^ 2 := by positivity
  have h6 : 0 < (1 - famLam t) * (1 - famBias t ^ 2) / 12 * (1 + 12 * (famChi t)⁻¹) /
      (1 + (famChi t)⁻¹) := by positivity
  linarith

theorem famSpinVar_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famSpinVar t := by
  rw [famSpinVar_eq_formula ht0 ht1]
  exact famVarFormula_pos ht0 ht1

/-- At `t = 0` the spin variance is `1/12`. -/
theorem famSpinVar_zero : famSpinVar 0 = 1 / 12 := by
  unfold famSpinVar
  rw [famLaw_zero]
  unfold regVar
  have e : ∀ j : Count, reference j * (meanCoordinate j - 0) ^ 2 =
      ((12).choose j.val : ℝ) / 4096 * (((2 * (j.val : ℝ) - 12) / 12)) ^ 2 := by
    intro j; rw [meanCoordinate_eq_real, reference_eq]; ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((Nat.choose 12 j : ℕ) : ℝ) / 4096 * (((2 * (j : ℝ) - 12) / 12)) ^ 2) 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

theorem famVarFormula_zero : famVarFormula 0 = 1 / 12 := by
  simp [famVarFormula]

theorem reference_mean : mean reference = 0 := by
  unfold mean
  have e : ∀ j : Count, meanCoordinate j * reference j =
      (((2 * (j.val : ℝ) - 12) / 12)) * (((12).choose j.val : ℝ) / 4096) := by
    intro j; rw [meanCoordinate_eq_real, reference_eq]
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (((2 * (j : ℝ) - 12) / 12)) * (((Nat.choose 12 j : ℕ) : ℝ) / 4096)) 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

theorem reference_feasibleAt : FeasibleAt 0 reference :=
  ⟨reference_feasible, reference_mean⟩

/-- `p(t)` is feasible with mean `t` for every `0 ≤ t < 1` (at `t = 0` it is the fair vector). -/
theorem famLaw_feasibleAt_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    FeasibleAt t (famLaw t) := by
  rcases ht0.eq_or_lt with h | h
  · subst h; rw [famLaw_zero]; exact reference_feasibleAt
  · exact famLaw_feasibleAt h ht1

theorem famLaw_pos_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (j : Count) :
    0 < famLaw t j := by
  rcases ht0.eq_or_lt with h | h
  · subst h; rw [famLaw_zero]; exact reference_pos j
  · exact famLaw_pos h ht1 j

theorem famSpinVar_pos_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 < famSpinVar t := by
  rcases ht0.eq_or_lt with h | h
  · subst h; rw [famSpinVar_zero]; norm_num
  · exact famSpinVar_pos h ht1

end BecknerOnofri.V2.FiniteState

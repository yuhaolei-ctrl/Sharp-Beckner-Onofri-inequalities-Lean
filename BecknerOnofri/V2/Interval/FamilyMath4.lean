module

public import BecknerOnofri.V2.Interval.FamilySpec3

@[expose] public section

/-!
# Mathematical identification, phase 4: spin variance, regression slope, residuals
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin Finset

theorem regVar_formula {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    regVar (famLaw t) meanCoordinate t = famVarFormula t := by
  rcases h0.eq_or_lt with h | h
  · subst h
    have := famSpinVar_zero
    unfold famSpinVar at this
    rw [this, famVarFormula_zero]
  · exact famSpinVar_eq_formula h h1

noncomputable def xtVal (t : ℝ) (j : ℕ) : ℝ := (((j : ℤ) - 6 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) + -t
noncomputable def etVal (t : ℝ) (j : ℕ) : ℝ := psVal t j * xtVal t j * gF t j
noncomputable def esVal (t : ℝ) : ℝ := ∑ j ∈ range 13, etVal t j
/-- The residual of the program, given the mean `M` and slope `η`. -/
noncomputable def eVal (M η t : ℝ) (j : ℕ) : ℝ := gF t j + -M + -(η * xtVal t j)

theorem xtVal_fin (t : ℝ) (j : Count) : xtVal t j.val = meanCoordinate j - t := by
  unfold xtVal
  rw [meanCoordinate_eq_real]
  push_cast
  ring

theorem gF_fin (t : ℝ) (j : Count) : gF t j.val = gradient (famLaw t) j := by
  simp [gF]

theorem esVal_eq (t : ℝ) :
    esVal t = ∑ j : Count, famLaw t j * (meanCoordinate j - t) * gradient (famLaw t) j := by
  unfold esVal
  rw [sum_range13]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold etVal
  rw [psVal_fin, xtVal_fin, gF_fin]

theorem eta_eq (t : ℝ) :
    esVal t * (regVar (famLaw t) meanCoordinate t)⁻¹ =
      regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t := by
  unfold regSlope
  rw [esVal_eq, div_eq_mul_inv]

theorem eVal_eq (t : ℝ) (j : Count) :
    eVal (regMean (famLaw t) (gradient (famLaw t)))
      (regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t) t j.val = famResid t j := by
  unfold eVal famResid gradResid regResid
  rw [gF_fin, xtVal_fin]
  ring

/-- The residuals as a function on `ℕ`. -/
noncomputable def famResidF (t : ℝ) (j : ℕ) : ℝ := if hj : j < 13 then famResid t ⟨j, hj⟩ else 0

theorem eVal_famResidF (t : ℝ) {j : ℕ} (hj : j < 13) :
    eVal (regMean (famLaw t) (gradient (famLaw t)))
      (regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t) t j = famResidF t j := by
  have := eVal_eq t ⟨j, hj⟩
  simpa [famResidF, hj] using this

theorem var_eq (t : ℝ) :
    ∑ j ∈ range 13, psVal t j *
      eVal (regMean (famLaw t) (gradient (famLaw t)))
        (regSlope (famLaw t) meanCoordinate (gradient (famLaw t)) t) t j ^ 2 = famResidVar t := by
  unfold famResidVar
  rw [sum_range13]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [psVal_fin, eVal_eq]

end BecknerOnofri.V2.Interval

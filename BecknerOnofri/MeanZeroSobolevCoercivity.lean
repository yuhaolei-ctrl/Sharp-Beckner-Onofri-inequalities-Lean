import BecknerOnofri.ComplementSobolevCoercivity
import BecknerOnofri.FullHessianDecomposition

/-! Critical physical Sobolev norm is controlled by energy on the entire
mean-zero domain, including the full first shell. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.MeanZeroSobolevCoercivity
open ComplementHessian RawComplementGap

theorem sobolevTerm_le_energyTerm {d : ℕ} (h : Torus d → ℝ)
    (hm : MeanZero h) (k : Frequency d) :
    sobolevTerm ((d:ℝ)/2) h k ≤
      criticalWeightConstant d*(frequencyLength k^d*‖fourierCoeff h k‖^2) := by
  by_cases hk : k=0
  · subst k
    simp [sobolevTerm,FullHessianDecomposition.fourierCoeff_zero_of_meanZero h hm]
  · have hr := Legacy.BecknerOnofri.TorusSobolev.radius_one_le hk
    have he : frequencyLength k^2=(latticeSquare k:ℝ) := by
      unfold frequencyLength
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),← latticeSquare_cast]
    have hn : (1:ℝ) ≤ latticeSquare k := by
      change 1 ≤ frequencyLength k at hr
      nlinarith
    have hbase : 1+(2*Real.pi*frequencyLength k)^2 ≤
        (1+(2*Real.pi)^2)*(latticeSquare k:ℝ) := by
      rw [mul_pow,he]
      nlinarith
    have hw := Real.rpow_le_rpow (by positivity) hbase (by positivity : (0:ℝ)≤(d:ℝ)/2)
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)] at hw
    unfold sobolevTerm criticalWeightConstant
    rw [frequencyLength_pow_eq]
    nlinarith [mul_le_mul_of_nonneg_right hw (sq_nonneg ‖fourierCoeff h k‖)]

theorem sobolevNorm_sq_le_normalizedEnergy {d : ℕ} (hd : 0<d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) (hs : InSobolev ((d:ℝ)/2) h) (hm : MeanZero h) :
    sobolevNorm ((d:ℝ)/2) h^2 ≤ criticalWeightConstant d*normalizedPotentialEnergy h := by
  have hsum := (raw_normalizedEnergy_hasSum hd h hh).mul_left (criticalWeightConstant d)
  rw [← hsum.tsum_eq]
  unfold sobolevNorm
  rw [Real.sq_sqrt (tsum_nonneg (fun k => by unfold sobolevTerm; positivity))]
  exact hasSum_le (sobolevTerm_le_energyTerm h hm) hs.2.hasSum hsum.summable.hasSum

#print axioms sobolevNorm_sq_le_normalizedEnergy
end BecknerOnofri.HighDim.MeanZeroSobolevCoercivity

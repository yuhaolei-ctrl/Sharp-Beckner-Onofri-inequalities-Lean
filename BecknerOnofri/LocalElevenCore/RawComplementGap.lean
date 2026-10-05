import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.RawComplementGap
import BecknerOnofri.LocalElevenCore.GraphEnergy
import BecknerOnofri.LegacyBridge

/-! The complement spectral gap on the exact raw critical Sobolev domain. -/
noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.RawComplementGap

open BecknerOnofri.HighDim.RawComplementGap hiding normalizedEnergy_gap normalizedEnergy_nonneg raw_fourier_square_hasSum raw_normalizedEnergy_hasSum

open Legacy.BecknerOnofri.TorusSobolev

theorem raw_fourier_square_hasSum {d : ℕ} (h : Torus d → ℝ)
    (hh : MemLp h 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d => ‖fourierCoeff h k‖^2) (∫ x, (h x)^2 ∂torusMeasure d) := by
  let v := Bridge.potentialLp h hh
  have hs := Complex.hasSum_re (UnitAddTorus.hasSum_prod_mFourierCoeff v v)
  have hi : Integrable (fun x => conj (v x)*v x) (torusMeasure d) :=
    (Lp.memLp v).star.integrable_mul (Lp.memLp v)
  have he : (∫ x, conj (v x)*v x ∂torusMeasure d).re = ∫ x, (h x)^2 ∂torusMeasure d := by
    calc
      _ = ∫ x, (conj (v x)*v x).re ∂torusMeasure d := (integral_re hi).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Bridge.potentialLp_ae h hh] with x hx
        change v x = (h x : ℂ) at hx
        simp only [hx, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  have hf (k : Frequency d) :
      (conj (UnitAddTorus.mFourierCoeff v k)*UnitAddTorus.mFourierCoeff v k).re =
        ‖fourierCoeff h k‖^2 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [← fourierIsometry_apply, Bridge.potentialLp_fourier]
  change HasSum (fun k : Frequency d =>
    (conj (UnitAddTorus.mFourierCoeff v k)*UnitAddTorus.mFourierCoeff v k).re)
    ((∫ x, conj (v x)*v x ∂torusMeasure d).re) at hs
  simpa only [he, hf] using hs

theorem raw_normalizedEnergy_hasSum {d : ℕ} (hd : 0 < d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) :
    HasSum (fun k : Frequency d => frequencyLength k^d * ‖fourierCoeff h k‖^2)
      (normalizedPotentialEnergy h) := by
  have hs := Bridge.potentialLp_summable hd h hh
  have he : normalizedPotentialEnergy h = criticalEnergy (Bridge.potentialLp h hh.1) := by
    rw [normalizedPotentialEnergy, Bridge.potentialLp_energy hd h hh]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by positivity : (2*Real.pi:ℝ) ≠ 0))
  have hfun : weightedSquare (fourierIsometry d (Bridge.potentialLp h hh.1)) =
      (fun k : Frequency d => frequencyLength k^d * ‖fourierCoeff h k‖^2) := by
    funext k
    simp only [weightedSquare, Bridge.potentialLp_fourier, ← Bridge.frequencyLength_eq]
  rw [he, criticalEnergy, coefficientEnergy, hfun]
  rw [hfun] at hs
  exact hs.hasSum

/-- The full raw-domain energy controls every mean-zero, first-shell-free
variation with the actual discrete eigenvalue gap. -/
theorem normalizedEnergy_gap {d : ℕ} (hd : 11 ≤ d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) (hc : ComplementSupported (fourierCoeff h)) :
    32 * (∫ x, (h x)^2 ∂torusMeasure d) ≤ normalizedPotentialEnergy h := by
  apply hasSum_le _ ((raw_fourier_square_hasSum h hh.1).mul_left 32)
    (raw_normalizedEnergy_hasSum (by omega) h hh)
  intro k
  by_cases hk : ComplementFrequency k
  · exact mul_le_mul_of_nonneg_right (complement_eigenvalue_ge_thirtytwo hd hk) (sq_nonneg _)
  · simp [hc k hk]

theorem normalizedEnergy_nonneg {d : ℕ} (hd : 0 < d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) : 0 ≤ normalizedPotentialEnergy h := by
  rw [← (raw_normalizedEnergy_hasSum hd h hh).tsum_eq]
  apply tsum_nonneg
  intro k
  unfold frequencyLength
  positivity

#print axioms normalizedEnergy_gap
end BecknerOnofri.HighDim.LocalEleven.RawComplementGap

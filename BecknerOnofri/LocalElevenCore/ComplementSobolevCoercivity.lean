module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.ComplementSobolevCoercivity
public import BecknerOnofri.LocalElevenCore.ComplementHessian

@[expose] public section

/-! Physical H^(d/2) coercivity of the actual complementary Hessian. -/
noncomputable section

open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ComplementHessian

open BecknerOnofri.HighDim.ComplementHessian hiding criticalWeightConstant criticalWeightConstant_pos normalized_le_two_near_zero secondVariation_complement_bound secondVariation_complement_sobolev secondVariation_complement_uniform sobolevNorm_sq_le_normalizedEnergy sobolevTerm_le_energyTerm weighted_square_bound weighted_square_integrable
open BecknerOnofri.HighDim.RawComplementGap hiding normalizedEnergy_gap normalizedEnergy_nonneg raw_fourier_square_hasSum raw_normalizedEnergy_hasSum
open ContinuousGibbs RawComplementGap

def criticalWeightConstant (d : ℕ) : ℝ := (1+(2*Real.pi)^2)^((d:ℝ)/2)

theorem criticalWeightConstant_pos (d : ℕ) : 0 < criticalWeightConstant d :=
  Real.rpow_pos_of_pos (by positivity) _

theorem sobolevTerm_le_energyTerm {d : ℕ} (h : Torus d → ℝ)
    (hc : ComplementSupported (fourierCoeff h)) (k : Frequency d) :
    sobolevTerm ((d:ℝ)/2) h k ≤
      criticalWeightConstant d * (frequencyLength k^d*‖fourierCoeff h k‖^2) := by
  by_cases hk : ComplementFrequency k
  · have hn : (1:ℝ) ≤ latticeSquare k := by
      exact_mod_cast (show 1 ≤ latticeSquare k from (by have := complement_latticeSquare_ge_two hk; omega))
    have he : frequencyLength k^2 = (latticeSquare k:ℝ) := by
      unfold frequencyLength
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), ← latticeSquare_cast]
    have hbase : 1+(2*Real.pi*frequencyLength k)^2 ≤
        (1+(2*Real.pi)^2)*(latticeSquare k:ℝ) := by
      rw [mul_pow, he]
      nlinarith
    have hw := Real.rpow_le_rpow (by positivity) hbase (by positivity : (0:ℝ) ≤ (d:ℝ)/2)
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)] at hw
    unfold sobolevTerm criticalWeightConstant
    rw [frequencyLength_pow_eq]
    nlinarith [mul_le_mul_of_nonneg_right hw (sq_nonneg ‖fourierCoeff h k‖)]
  · simp [sobolevTerm, hc k hk]

theorem sobolevNorm_sq_le_normalizedEnergy {d : ℕ} (hd : 0 < d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) (hs : InSobolev ((d:ℝ)/2) h)
    (hc : ComplementSupported (fourierCoeff h)) :
    sobolevNorm ((d:ℝ)/2) h ^ 2 ≤ criticalWeightConstant d * normalizedPotentialEnergy h := by
  have hsum := (raw_normalizedEnergy_hasSum hd h hh).mul_left (criticalWeightConstant d)
  rw [← hsum.tsum_eq]
  unfold sobolevNorm
  rw [Real.sq_sqrt (tsum_nonneg (fun k => by unfold sobolevTerm; positivity))]
  exact hasSum_le (sobolevTerm_le_energyTerm h hc) hs.2.hasSum hsum.summable.hasSum

theorem secondVariation_complement_sobolev {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ (u : Space d) in 𝓝 0, ∀ μ : ℝ, 0 < μ → μ ≤ 2 →
      ∀ h : Torus d → ℝ, InCriticalSobolev h → InSobolev ((d:ℝ)/2) h →
        ComplementSupported (fourierCoeff h) →
        secondVariation (μ*spectralThreshold d) u h ≤
          -(7/(16*criticalWeightConstant d):ℝ)*sobolevNorm ((d:ℝ)/2) h ^ 2 := by
  filter_upwards [secondVariation_complement_uniform hd] with u hu
  intro μ hμ hμ2 h hh hs hc
  have hhess := hu μ hμ hμ2 h hh hc
  have hnorm := sobolevNorm_sq_le_normalizedEnergy (by omega) h hh hs hc
  have hC := criticalWeightConstant_pos d
  have hbound : sobolevNorm ((d:ℝ)/2) h ^ 2 / criticalWeightConstant d ≤ normalizedPotentialEnergy h := by
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hnorm)
  have hmul := mul_le_mul_of_nonpos_left hbound (by norm_num : -(7/16:ℝ) ≤ 0)
  apply hhess.trans
  convert! hmul using 1 <;> ring

#print axioms secondVariation_complement_sobolev
end BecknerOnofri.HighDim.LocalEleven.ComplementHessian

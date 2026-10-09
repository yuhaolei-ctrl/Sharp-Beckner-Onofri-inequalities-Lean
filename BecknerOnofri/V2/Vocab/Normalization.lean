module

public import BecknerOnofri.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

/-! # The normalization `c_d ‖ρ‖²_{Ḣ^{-d/2}} = spectralEnergy ρ / β_s(d)`, `c_d β_s(d) = (2π)^d`

Matched definitions (all from `BecknerOnofri.Statement`, i.e. `Challenge.lean`):
* `spectralThreshold d = 2 * π ^ ((d:ℝ)/2) / Real.Gamma ((d:ℝ)/2)`   (`β_s(d)`),
* `spectralTerm ρ k = (frequencyLength k ^ d)⁻¹ * ‖fourierCoeff ρ.value k‖ ^ 2`,
* `spectralEnergy ρ = ∑' k : NonzeroFrequency d, ENNReal.ofReal (spectralTerm ρ k)`.
The manuscript constant `c_d = 2^{d-1} π^{d/2} Γ(d/2)` (eq:intro-kernel) is not defined in the
repository; `kernelConstant` below is the new definition, with natural-number power `2^(d-1)`
(natural subtraction is harmless: `d ≥ 1` throughout) and real powers of `π`. -/

noncomputable section
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab
open BecknerOnofri.HighDim

/-- `c_d = 2^{d-1} π^{d/2} Γ(d/2)`. -/
def kernelConstant (d : ℕ) : ℝ :=
  2 ^ (d - 1) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)

lemma kernelConstant_pos {d : ℕ} (hd : 0 < d) : 0 < kernelConstant d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold kernelConstant
  have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
  positivity

/-- `c_d β_s(d) = (2π)^d`, with the actual `Real.Gamma` and real powers. -/
theorem kernelConstant_mul_spectralThreshold {d : ℕ} (hd : 0 < d) :
    kernelConstant d * spectralThreshold d = (2 * Real.pi) ^ d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hπ := Real.pi_pos
  have hΓ : 0 < Real.Gamma ((d : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
  have ha : Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ ((d : ℝ) / 2) = Real.pi ^ d := by
    rw [← Real.rpow_add hπ, show (d : ℝ) / 2 + (d : ℝ) / 2 = (d : ℝ) by ring]
    exact Real.rpow_natCast Real.pi d
  have h2 : (2 : ℝ) ^ (d - 1) * 2 = 2 ^ d := by
    rw [← pow_succ]
    congr 1
    omega
  unfold kernelConstant spectralThreshold
  rw [mul_pow, ← h2, ← ha]
  field_simp

/-- `‖f‖²_{Ḣ^{-d/2}} = Σ_{k≠0} (2π|k|)^{-d} |f̂(k)|²` (eq:intro-primal-energy with `s = -d/2`),
as an extended nonnegative sum (value `⊤` when divergent). -/
def negSobolevEnergy {d : ℕ} (f : Torus d → ℝ) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d,
    ENNReal.ofReal (((2 * Real.pi * frequencyLength k.val) ^ d)⁻¹ * ‖fourierCoeff f k.val‖ ^ 2)


/-- `negSobolevEnergy` is literally eq:intro-primal-energy at `s = -d/2`, with the real power
`(2π|k|)^{2s}`. -/
theorem negSobolevEnergy_eq_rpow {d : ℕ} (f : Torus d → ℝ) :
    negSobolevEnergy f = ∑' k : NonzeroFrequency d,
      ENNReal.ofReal ((2 * Real.pi * frequencyLength k.val) ^ (2 * (-(d : ℝ) / 2)) *
        ‖fourierCoeff f k.val‖ ^ 2) := by
  unfold negSobolevEnergy
  refine tsum_congr fun k => ?_
  congr 2
  rw [show 2 * (-(d : ℝ) / 2) = -(d : ℝ) by ring, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

/-- `spectralEnergy ρ = (2π)^d ‖ρ‖²_{Ḣ^{-d/2}}`. -/
theorem spectralEnergy_eq_mul_negSobolevEnergy {d : ℕ} (ρ : ProbabilityDensity d) :
    spectralEnergy ρ = ENNReal.ofReal ((2 * Real.pi) ^ d) * negSobolevEnergy ρ.value := by
  unfold spectralEnergy negSobolevEnergy
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold spectralTerm
  have hne : ((2 * Real.pi) ^ d : ℝ) ≠ 0 := by positivity
  rw [mul_pow (2 * Real.pi) (frequencyLength k.val) d, mul_inv]
  field_simp

/-- The seminorm is finite exactly when the repository's `spectralEnergy` is finite. -/
theorem negSobolevEnergy_ne_top_iff {d : ℕ} (ρ : ProbabilityDensity d) :
    negSobolevEnergy ρ.value ≠ ∞ ↔ spectralEnergy ρ ≠ ∞ := by
  rw [spectralEnergy_eq_mul_negSobolevEnergy]
  constructor
  · intro h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
  · intro h hq
    rw [hq] at h
    have hpos : 0 < (2 * Real.pi) ^ d := by positivity
    exact h (ENNReal.mul_top (by simpa using hpos))

/-- The normalization identity, in `ℝ≥0∞`:
`c_d ‖ρ‖²_{Ḣ^{-d/2}} = spectralEnergy ρ / β_s(d)`. -/
theorem kernelConstant_mul_negSobolevEnergy {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d) :
    ENNReal.ofReal (kernelConstant d) * negSobolevEnergy ρ.value =
      spectralEnergy ρ / ENNReal.ofReal (spectralThreshold d) := by
  have hβ : 0 < spectralThreshold d := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    unfold spectralThreshold
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
    positivity
  rw [ENNReal.eq_div_iff (by simpa using hβ) ENNReal.ofReal_ne_top,
    spectralEnergy_eq_mul_negSobolevEnergy, ← kernelConstant_mul_spectralThreshold hd,
    ENNReal.ofReal_mul (kernelConstant_pos hd).le]
  ring

/-- Real form: `c_d ‖ρ‖² = (spectralEnergy ρ).toReal / β_s(d)` (both sides `0` if divergent). -/
theorem kernelConstant_mul_negSobolevEnergy_toReal {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) :
    kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      (spectralEnergy ρ).toReal / spectralThreshold d := by
  have h := congrArg ENNReal.toReal (kernelConstant_mul_negSobolevEnergy hd ρ)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (kernelConstant_pos hd).le, ENNReal.toReal_div,
    ENNReal.toReal_ofReal] at h
  · exact h
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    unfold spectralThreshold
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
    positivity

end BecknerOnofri.V2.Vocab

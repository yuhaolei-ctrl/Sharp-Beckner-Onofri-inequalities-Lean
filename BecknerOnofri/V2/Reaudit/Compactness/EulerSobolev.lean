module

public import BecknerOnofri.UniformFourierHessian

@[expose] public section

/-! # The Euler multiplier estimate `‖u‖_{H^d} ≤ C β ‖ρ - 1‖_{L²}`

Manuscript (Section 4, proof of `prop:section4-first-order-coexistence`):
"The Euler--Lagrange relation gives `u_n = β_n g * (ρ_n - 1)` (`eq:section4-un-Euler`).  The Fourier
multipliers `eq:section4-T-multipliers` therefore give
`‖u_n‖_{H^{11}} ≤ C β_n ‖ρ_n - 1‖_{L²(m_{11})} → 0`" (`eq:section4-un-H11-convergence`).

Here `g` has the symbol `ĝ(k) = 1/(β_s |k|^d)` (`k ≠ 0`), i.e. `β g * f = (β/β_s) · greenContinuous f`,
and the constant is `C_d = (1 + 4π²)^{d/2}/β_s`: for `k ≠ 0` one has `|k| ≥ 1`, hence
`(1 + (2π|k|)²)^d ≤ (1 + 4π²)^d |k|^{2d}`.  The statement is for a continuous potential `u` of the form
`u = c · greenContinuous h` (for the Euler equation, `h = ρ - 1`, `c = β/β_s`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace BecknerOnofri.V2.Reaudit.Compactness
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell

variable {d : ℕ}

theorem one_le_frequencyLength (hd : 0 < d) {k : Frequency d} (hk : k ≠ 0) : 1 ≤ frequencyLength k := by
  have h := GreenCritical.nonzero_eigenvalue_ge_one (⟨k, hk⟩ : NonzeroFrequency d)
  by_contra hlt
  push Not at hlt
  have h0 : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  exact absurd h (not_le.2 (pow_lt_one₀ h0 hlt hd.ne'))

/-- **`eq:section4-un-H11-convergence`, Fourier-multiplier estimate.**  If `u = c · G h` with `G` the
Green multiplier `1/|k|^d` and `h` continuous, then `u ∈ H^d` and
`‖u‖_{H^d} ≤ (1 + 4π²)^{d/2} |c| ‖h‖_{L²}`. -/
theorem sobolev_green_bound (hd : 0 < d) (c : ℝ) (h u : Space d) (hu : u = c • greenContinuous d h) :
    InSobolev (d : ℝ) u ∧
      sobolevNorm (d : ℝ) u ≤
        Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ d) * |c| * Real.sqrt (∫ x, (h x) ^ 2 ∂torusMeasure d) := by
  set C : ℝ := (1 + (2 * Real.pi) ^ 2) ^ d with hC
  have hCpos : 0 < C := by positivity
  -- Fourier coefficients of `u`
  have hcoef : ∀ k : Frequency d, ‖fourierCoeff u k‖ =
      |c| * ((if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ)) * ‖fourierCoeff h k‖ := by
    intro k
    rw [← coefficient_eq_fourierCoeff, ← coefficient_eq_fourierCoeff, hu, map_smul,
      coefficient_green hd, Complex.real_smul, norm_mul, Complex.norm_real, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have : 0 ≤ (if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) := by
      split_ifs
      · exact le_rfl
      · have : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
        positivity
    rw [abs_of_nonneg this]
    ring
  -- the weighted term is bounded by `C c² |ĥ(k)|²`
  have hterm : ∀ k : Frequency d, sobolevTerm (d : ℝ) u k ≤ C * c ^ 2 * ‖fourierCoeff h k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · simp only [sobolevTerm, hcoef, hk, ite_true]
      simp only [mul_zero, zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero]
      positivity
    · have hL := one_le_frequencyLength hd hk
      have hL0 : 0 < frequencyLength k := lt_of_lt_of_le one_pos hL
      rw [sobolevTerm, Real.rpow_natCast, hcoef, if_neg hk]
      have h1 : (1 + (2 * Real.pi * frequencyLength k) ^ 2) ≤
          (1 + (2 * Real.pi) ^ 2) * frequencyLength k ^ 2 := by
        nlinarith [sq_nonneg (2 * Real.pi), mul_pow (2 * Real.pi) (frequencyLength k) 2]
      have h2 : (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ d ≤
          C * (frequencyLength k ^ d) ^ 2 := by
        calc (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ d
            ≤ ((1 + (2 * Real.pi) ^ 2) * frequencyLength k ^ 2) ^ d :=
              pow_le_pow_left₀ (by positivity) h1 d
          _ = C * (frequencyLength k ^ d) ^ 2 := by
              rw [mul_pow, hC, ← pow_mul, ← pow_mul, mul_comm 2 d]
      have hp : 0 < frequencyLength k ^ d := pow_pos hL0 d
      calc (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ d *
            (|c| * (1 / frequencyLength k ^ d) * ‖fourierCoeff h k‖) ^ 2
          ≤ C * (frequencyLength k ^ d) ^ 2 *
            (|c| * (1 / frequencyLength k ^ d) * ‖fourierCoeff h k‖) ^ 2 := by
            gcongr
        _ = C * c ^ 2 * ‖fourierCoeff h k‖ ^ 2 := by
            field_simp
            rw [sq_abs]
            ring
  have hps := UniformFourier.parseval h
  have hsum : Summable (sobolevTerm (d : ℝ) u) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (sq_nonneg _)) hterm
      (hps.summable.mul_left (C * c ^ 2))
  refine ⟨⟨u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), hsum⟩, ?_⟩
  have htsum : ∑' k, sobolevTerm (d : ℝ) u k ≤ C * c ^ 2 * ∫ x, (h x) ^ 2 ∂torusMeasure d := by
    calc ∑' k, sobolevTerm (d : ℝ) u k ≤ ∑' k, C * c ^ 2 * ‖fourierCoeff h k‖ ^ 2 :=
          hsum.tsum_le_tsum hterm (hps.summable.mul_left _)
      _ = C * c ^ 2 * ∫ x, (h x) ^ 2 ∂torusMeasure d := by
          rw [tsum_mul_left, hps.tsum_eq]
  unfold sobolevNorm
  calc Real.sqrt (∑' k, sobolevTerm (d : ℝ) u k)
      ≤ Real.sqrt (C * c ^ 2 * ∫ x, (h x) ^ 2 ∂torusMeasure d) := Real.sqrt_le_sqrt htsum
    _ = Real.sqrt C * |c| * Real.sqrt (∫ x, (h x) ^ 2 ∂torusMeasure d) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ C * c ^ 2), Real.sqrt_mul hCpos.le,
          Real.sqrt_sq_eq_abs]

end BecknerOnofri.V2.Reaudit.Compactness

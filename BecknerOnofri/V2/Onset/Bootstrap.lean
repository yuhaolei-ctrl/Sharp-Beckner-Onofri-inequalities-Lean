module

public import BecknerOnofri.V2.Onset.SobolevExp
public import BecknerOnofri.LocalElevenCore.WeightedExponentialRemainder

@[expose] public section

/-! # The Sobolev-algebra bootstrap for the Euler equation (Proposition 5.24)

Manuscript (Proof of Proposition 5.24, `eq:section5-onset-elliptic-equation`,
`eq:section5-onset-uniform-smoothness`, via Corollary 2.6): for a mean-zero solution of
`(2π)^{-d}(-Δ)^{d/2} u = τ (ρ_u - 1)`, "`H^{jd}` is a Banach algebra embedded in `L^∞`.  Hence
`u ∈ H^{jd}` implies `e^u ∈ H^{jd}` and therefore `ρ ∈ H^{jd}`; the Euler-Lagrange equation then gives
`u ∈ H^{(j+1)d}`."

Here the quantitative version is proved, with constants depending only on `(d, j)` and the bounds
on the coupling `|τ| ≤ T` and on `‖u‖_{H^d}`:

* `sobolev_normalized_space` : `‖e^u/Z(u)‖_{H^s} ≤ exp(C_{d,s}‖u‖_{H^s})` for mean-zero `u`;
* `sobolev_euler_step` : the Fourier-multiplier step `‖u‖_{H^{s+d}} ≤ E_d |τ| ‖ρ‖_{H^s}`;
* `sobolev_bootstrap` : by induction, `‖u‖_{H^{(m+1)d}} ≤ bootBound d T B m`.

The multiplier step uses the Euler equation in the repository form
`|k|^d û(k) = (β/β_s(d)) ρ̂(k)`, `k ≠ 0` (`OptimizerDuality.raw_optimizer_euler`), where
`τ = β/β_s(d)`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

/-! ## Scalar multiples -/

theorem sobSq_smul {d : ℕ} (s c : ℝ) (a : Frequency d → ℂ) :
    sobSq s (fun k => c • a k) = ENNReal.ofReal (c ^ 2) * sobSq s a := by
  unfold sobSq
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hw : 0 ≤ sobolevScale s k := (sobolevScale_pos s k).le
  have : sobolevScale s k * ‖c • a k‖ = |c| * (sobolevScale s k * ‖a k‖) := by
    rw [norm_smul, Real.norm_eq_abs]; ring
  rw [this, ENNReal.ofReal_mul (abs_nonneg c), mul_pow, ← ENNReal.ofReal_pow (abs_nonneg c),
    sq_abs]

section Space
open ContinuousGibbs ContinuousFirstShell

/-- **The normalized Gibbs density in `H^s`, `s > d/2`**:
`‖e^u / Z(u)‖_{H^s} ≤ exp(C_{d,s} ‖u‖_{H^s})` for mean-zero `u ∈ H^s`. -/
theorem sobolev_normalized_space {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) (u : Space d)
    (hu : InSobolev s u) (hm : mean d u = 0) :
    InSobolev s (⇑(normalized u)) ∧
      sobolevNorm s (⇑(normalized u)) ≤ Real.exp (sobolevAlgConst d s * sobolevNorm s (⇑u)) := by
  obtain ⟨he1, he2⟩ := sobolev_exp_space hd hs u hu
  have hZ : 1 ≤ partition u := WeightedExponentialRemainder.partition_ge_one u hm
  have hZ0 : 0 < partition u := partition_pos u
  have hcoef : fourierCoeff (⇑(normalized u)) =
      fun k => (partition u)⁻¹ • fourierCoeff (⇑(exponential u)) k := by
    rw [fourierCoeff_eq_coefficient, fourierCoeff_eq_coefficient]
    funext k
    simp only [normalized, map_smul]
  have hsq : sobSq s (fourierCoeff (⇑(normalized u))) =
      ENNReal.ofReal (((partition u)⁻¹) ^ 2) * sobSq s (fourierCoeff (⇑(exponential u))) := by
    rw [hcoef, sobSq_smul]
  have hfin : sobSq s (fourierCoeff (⇑(normalized u))) ≠ ⊤ := by
    rw [hsq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((inSobolev_iff _).mp he1).2
  have hmem : InSobolev s (⇑(normalized u)) :=
    (inSobolev_iff _).mpr ⟨ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ (normalized u), hfin⟩
  refine ⟨hmem, ?_⟩
  have h2 : sobolevNorm s (⇑(normalized u)) ^ 2 ≤ sobolevNorm s (⇑(exponential u)) ^ 2 := by
    rw [sobolevNorm_sq_eq hmem, sobolevNorm_sq_eq he1, hsq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
    have : ((partition u)⁻¹) ^ 2 ≤ 1 := by
      have := inv_le_one_of_one_le₀ hZ
      nlinarith [inv_nonneg.mpr hZ0.le]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg this
  refine le_trans ?_ he2
  exact (pow_le_pow_iff_left₀ (sobolevNorm_nonneg' _ _) (sobolevNorm_nonneg' _ _)
    two_ne_zero).mp h2

end Space

/-! ## The Fourier multiplier step -/

theorem one_le_frequencyLength {d : ℕ} {k : Frequency d} (hk : k ≠ 0) : 1 ≤ frequencyLength k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hk (funext h)
  have h1 : (1:ℝ) ≤ (k i : ℝ) ^ 2 := by
    have : (1:ℤ) ≤ (k i) ^ 2 := by nlinarith [sq_pos_of_ne_zero hi]
    exact_mod_cast this
  have h2 : (k i : ℝ) ^ 2 ≤ ∑ j : Fin d, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => (k j : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  unfold frequencyLength
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (h1.trans h2)

/-- The constant of the multiplier step: `(1 + 4π²)^{d/2}`. -/
def eulerConst (d : ℕ) : ℝ := Real.sqrt ((1 + 4 * Real.pi ^ 2) ^ d)

theorem eulerConst_nonneg (d : ℕ) : 0 ≤ eulerConst d := Real.sqrt_nonneg _

theorem fourierCoeff_zero_meanZero {d : ℕ} {u : Torus d → ℝ} (hm : MeanZero u) :
    fourierCoeff u 0 = 0 := by
  unfold BecknerOnofri.HighDim.fourierCoeff
  have h : ∀ x, UnitAddTorus.mFourier (-(0 : Frequency d)) x * (u x : ℂ) = ((u x : ℝ) : ℂ) := by
    intro x; simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul]
  simp_rw [h]
  have h0 : (∫ x, u x ∂torusMeasure d) = 0 := hm
  have h1 := integral_ofReal (𝕜 := ℂ) (μ := torusMeasure d) (f := fun x => u x)
  rw [h0] at h1
  exact h1.trans (by simp)

/-- **Euler multiplier step** (`eq:section5-onset-elliptic-equation`): if the mean-zero `u` solves
`|k|^d û(k) = c ρ̂(k)` for `k ≠ 0` with `ρ ∈ H^s`, then `u ∈ H^{s+d}` and
`‖u‖_{H^{s+d}} ≤ (1+4π²)^{d/2} |c| ‖ρ‖_{H^s}`. -/
theorem sobolev_euler_step {d : ℕ} (s c : ℝ) (u ρ : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d))
    (hm : MeanZero u) (hρ : InSobolev s ρ)
    (heuler : ∀ k : Frequency d, k ≠ 0 →
      ((frequencyLength k : ℂ) ^ d) * fourierCoeff u k = (c : ℂ) * fourierCoeff ρ k) :
    InSobolev (s + d) u ∧ sobolevNorm (s + d) u ≤ eulerConst d * |c| * sobolevNorm s ρ := by
  set B : ℝ := (1 + 4 * Real.pi ^ 2) ^ d * c ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ k : Frequency d, sobolevTerm (s + d) u k ≤ B * sobolevTerm s ρ k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp only [sobolevTerm, fourierCoeff_zero_meanZero hm, norm_zero]
      have : 0 ≤ B * ((1 + (2 * Real.pi * frequencyLength (0 : Frequency d)) ^ 2) ^ s *
          ‖HighDim.fourierCoeff ρ 0‖ ^ 2) := by positivity
      simpa using this
    · have hl := one_le_frequencyLength hk
      set x := (1 + (2 * Real.pi * frequencyLength k) ^ 2) with hx
      have hx0 : 0 < x := by positivity
      have hx1 : x ≤ (1 + 4 * Real.pi ^ 2) * frequencyLength k ^ 2 := by
        have : 1 ≤ frequencyLength k ^ 2 := by nlinarith
        rw [hx]; nlinarith [Real.pi_pos]
      have hxd : x ^ d ≤ (1 + 4 * Real.pi ^ 2) ^ d * (frequencyLength k ^ d) ^ 2 := by
        calc x ^ d ≤ ((1 + 4 * Real.pi ^ 2) * frequencyLength k ^ 2) ^ d :=
              pow_le_pow_left₀ hx0.le hx1 d
          _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 d]
      have hnorm : frequencyLength k ^ d * ‖fourierCoeff u k‖ = |c| * ‖fourierCoeff ρ k‖ := by
        have := congrArg norm (heuler k hk)
        have hf0 : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf0] at this
        exact this
      have hrpow : x ^ (s + d) = x ^ s * x ^ d := by
        rw [Real.rpow_add hx0, Real.rpow_natCast]
      simp only [sobolevTerm]
      rw [← hx, hrpow]
      calc x ^ s * x ^ d * ‖fourierCoeff u k‖ ^ 2
          ≤ x ^ s * ((1 + 4 * Real.pi ^ 2) ^ d * (frequencyLength k ^ d) ^ 2) *
              ‖fourierCoeff u k‖ ^ 2 := by gcongr
        _ = (1 + 4 * Real.pi ^ 2) ^ d * x ^ s * (frequencyLength k ^ d * ‖fourierCoeff u k‖) ^ 2 := by
            ring
        _ = B * (x ^ s * ‖fourierCoeff ρ k‖ ^ 2) := by
            rw [hnorm, hB, mul_pow, sq_abs]; ring
  have hsum : Summable (sobolevTerm (s + d) u) :=
    Summable.of_nonneg_of_le (fun k => by rw [sobolevTerm_eq]; positivity) hterm
      (hρ.2.mul_left B)
  have hmem : InSobolev (s + d) u := ⟨hu, hsum⟩
  refine ⟨hmem, ?_⟩
  have hle : ∑' k, sobolevTerm (s + d) u k ≤ B * ∑' k, sobolevTerm s ρ k := by
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hterm (hρ.2.mul_left B)
  unfold sobolevNorm
  calc Real.sqrt (∑' k, sobolevTerm (s + d) u k) ≤ Real.sqrt (B * ∑' k, sobolevTerm s ρ k) :=
        Real.sqrt_le_sqrt hle
    _ = eulerConst d * |c| * Real.sqrt (∑' k, sobolevTerm s ρ k) := by
        rw [Real.sqrt_mul hB0, hB, Real.sqrt_mul (by positivity), eulerConst, Real.sqrt_sq_eq_abs]


/-! ## The bootstrap -/

/-- The bound on `‖u‖_{H^{(m+1)d}}` produced by `m` bootstrap steps from a bound `B` on `‖u‖_{H^d}`
and `|τ| ≤ T`. -/
def bootBound (d : ℕ) (T B : ℝ) : ℕ → ℝ
  | 0 => B
  | m + 1 => eulerConst d * T *
      Real.exp (sobolevAlgConst d (((m : ℝ) + 1) * d) * bootBound d T B m)

section Space
open ContinuousGibbs ContinuousFirstShell

/-- **Sobolev-algebra bootstrap** (`eq:section5-onset-uniform-smoothness`, the induction in the
proof of Proposition 5.24): a mean-zero continuous `u ∈ H^d` solving the Euler equation
`|k|^d û(k) = c ρ̂_u(k)` (`k ≠ 0`) with `|c| ≤ T` and `‖u‖_{H^d} ≤ B` lies in every `H^{(m+1)d}`,
with the explicit bound `bootBound d T B m`, which depends only on `d, T, B, m`. -/
theorem sobolev_bootstrap {d : ℕ} (hd : 0 < d) (T B c : ℝ) (hc : |c| ≤ T) (u : Space d)
    (hm : mean d u = 0)
    (heuler : ∀ k : Frequency d, k ≠ 0 →
      ((frequencyLength k : ℂ) ^ d) * fourierCoeff (⇑u) k =
        (c : ℂ) * fourierCoeff (normalizedGibbs (⇑u)) k)
    (hu1 : InSobolev (d : ℝ) (⇑u)) (hB : sobolevNorm (d : ℝ) (⇑u) ≤ B) :
    ∀ m : ℕ, InSobolev (((m : ℝ) + 1) * d) (⇑u) ∧
      sobolevNorm (((m : ℝ) + 1) * d) (⇑u) ≤ bootBound d T B m := by
  intro m
  induction m with
  | zero => simpa [bootBound] using ⟨hu1, hB⟩
  | succ m ih =>
    obtain ⟨hum, hbm⟩ := ih
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    have hs : (d : ℝ) / 2 < ((m : ℝ) + 1) * d := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    obtain ⟨hρ1, hρ2⟩ := sobolev_normalized_space hd hs u hum hm
    have hm' : MeanZero (⇑u) := by simpa [MeanZero, mean_apply] using hm
    have hfun : (⇑(normalized u) : Torus d → ℝ) = normalizedGibbs (⇑u) := funext (normalized_apply u)
    have hE := sobolev_euler_step (((m : ℝ) + 1) * d) c (⇑u) (⇑(normalized u))
      (ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ u) hm' hρ1 (by
        intro k hk
        rw [hfun]
        exact heuler k hk)
    have hsd : ((m : ℝ) + 1) * d + d = (((m + 1 : ℕ) : ℝ) + 1) * d := by push_cast; ring
    rw [hsd] at hE
    refine ⟨hE.1, hE.2.trans ?_⟩
    have hC := sobolevAlgConst_nonneg d (((m : ℝ) + 1) * d)
    have hexp : sobolevNorm (((m : ℝ) + 1) * d) (⇑(normalized u)) ≤
        Real.exp (sobolevAlgConst d (((m : ℝ) + 1) * d) * bootBound d T B m) :=
      hρ2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbm hC))
    have hT : 0 ≤ T := (abs_nonneg c).trans hc
    show _ ≤ eulerConst d * T * Real.exp (sobolevAlgConst d (((m : ℝ) + 1) * d) * bootBound d T B m)
    have h1 : eulerConst d * |c| ≤ eulerConst d * T :=
      mul_le_mul_of_nonneg_left hc (eulerConst_nonneg d)
    calc eulerConst d * |c| * sobolevNorm (((m : ℝ) + 1) * d) (⇑(normalized u))
        ≤ (eulerConst d * T) * sobolevNorm (((m : ℝ) + 1) * d) (⇑(normalized u)) :=
          mul_le_mul_of_nonneg_right h1 (sobolevNorm_nonneg' _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg (eulerConst_nonneg d) hT)

end Space

end BecknerOnofri.V2.Onset

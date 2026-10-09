module

public import BecknerOnofri.V2.Onset.SobolevAlgebra
public import BecknerOnofri.LegacyBridge

@[expose] public section

/-! # Tail splitting for Sobolev norms (compactness step of Proposition 5.24)

Pointwise in the frequency, for `0 ≤ s ≤ s'` and a cut-off radius `R`,
`(1+(2π|k|)²)^s |û(k)|² ≤ (1+(2πR)²)^s |û(k)|² + (1+(2πR)²)^{s-s'} (1+(2π|k|)²)^{s'} |û(k)|²`.
Summing: an `L²`-small function with a bounded `H^{s'}` norm is `H^s`-small for `s < s'`.
This is the quantitative form of the Rellich-type step "convergence in `L²` plus a uniform
`H^{s'}` bound gives convergence in `H^s`" used in the proof of Proposition 5.24. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

theorem sobolevTerm_tail_le {d : ℕ} {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (R : ℝ)
    (u : Torus d → ℝ) (k : Frequency d) :
    sobolevTerm s u k ≤ (1 + (2 * Real.pi * R) ^ 2) ^ s * ‖fourierCoeff u k‖ ^ 2 +
      (1 + (2 * Real.pi * R) ^ 2) ^ (s - s') * sobolevTerm s' u k := by
  set A : ℝ := 1 + (2 * Real.pi * R) ^ 2 with hA
  set w : ℝ := 1 + (2 * Real.pi * frequencyLength k) ^ 2 with hw
  have hA0 : 0 < A := by positivity
  have hw0 : 0 < w := by positivity
  have hc : 0 ≤ ‖fourierCoeff u k‖ ^ 2 := by positivity
  have e1 : sobolevTerm s u k = w ^ s * ‖fourierCoeff u k‖ ^ 2 := rfl
  have e2 : sobolevTerm s' u k = w ^ s' * ‖fourierCoeff u k‖ ^ 2 := rfl
  rw [e1, e2]
  have h2 : 0 ≤ A ^ (s - s') * (w ^ s' * ‖fourierCoeff u k‖ ^ 2) := by positivity
  have h1 : 0 ≤ A ^ s * ‖fourierCoeff u k‖ ^ 2 := by positivity
  rcases le_or_gt w A with h | h
  · have : w ^ s ≤ A ^ s := Real.rpow_le_rpow hw0.le h hs
    nlinarith [mul_le_mul_of_nonneg_right this hc]
  · have e : w ^ s = w ^ s' * w ^ (s - s') := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have : w ^ (s - s') ≤ A ^ (s - s') :=
      Real.rpow_le_rpow_of_nonpos hA0 h.le (by linarith)
    have h3 : w ^ s * ‖fourierCoeff u k‖ ^ 2 ≤ A ^ (s - s') * (w ^ s' * ‖fourierCoeff u k‖ ^ 2) := by
      rw [e]
      have := mul_le_mul_of_nonneg_right this (mul_nonneg (Real.rpow_nonneg hw0.le s') hc)
      nlinarith [this]
    linarith

/-- **Tail splitting.**  If `û ∈ ℓ²` and `u ∈ H^{s'}`, then `u ∈ H^s` for `0 ≤ s ≤ s'` and
`‖u‖²_{H^s} ≤ (1+(2πR)²)^s ∑|û|² + (1+(2πR)²)^{s-s'} ‖u‖²_{H^{s'}}`. -/
theorem sobolevNorm_sq_tail_le {d : ℕ} {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (R : ℝ)
    (u : Torus d → ℝ) (h0 : Summable fun k : Frequency d => ‖fourierCoeff u k‖ ^ 2)
    (hu' : InSobolev s' u) :
    InSobolev s u ∧
      sobolevNorm s u ^ 2 ≤ (1 + (2 * Real.pi * R) ^ 2) ^ s * ∑' k, ‖fourierCoeff u k‖ ^ 2 +
        (1 + (2 * Real.pi * R) ^ 2) ^ (s - s') * sobolevNorm s' u ^ 2 := by
  have hnn (t : ℝ) (k : Frequency d) : 0 ≤ sobolevTerm t u k := by
    rw [sobolevTerm_eq]; positivity
  have hsum : Summable fun k : Frequency d =>
      (1 + (2 * Real.pi * R) ^ 2) ^ s * ‖fourierCoeff u k‖ ^ 2 +
        (1 + (2 * Real.pi * R) ^ 2) ^ (s - s') * sobolevTerm s' u k :=
    (h0.mul_left _).add (hu'.2.mul_left _)
  have hsm : Summable (sobolevTerm s u) :=
    Summable.of_nonneg_of_le (hnn s) (sobolevTerm_tail_le hs hss R u) hsum
  refine ⟨⟨hu'.1, hsm⟩, ?_⟩
  have hsq (t : ℝ) (h : Summable (sobolevTerm t u)) :
      sobolevNorm t u ^ 2 = ∑' k, sobolevTerm t u k := by
    unfold sobolevNorm
    exact Real.sq_sqrt (tsum_nonneg (hnn t))
  rw [hsq s hsm, hsq s' hu'.2, ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (h0.mul_left _)
    (hu'.2.mul_left _)]
  exact hsm.tsum_le_tsum (sobolevTerm_tail_le hs hss R u) hsum

/-- **Parseval base case (Bessel).**  The Fourier coefficients of an `L²` function are square
summable. -/
theorem summable_sq_fourierCoeff {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    Summable fun k : Frequency d => ‖fourierCoeff u k‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞))
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d (Bridge.potentialLp u hu))
  refine (h.summable).congr fun k => ?_
  simp [Bridge.potentialLp_fourier]

/-- `H⁰ = L²` at the level of the repository predicate. -/
theorem inSobolev_zero_iff {d : ℕ} (u : Torus d → ℝ) :
    InSobolev 0 u ↔ MemLp u 2 (torusMeasure d) := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  refine (summable_sq_fourierCoeff u h).congr fun k => ?_
  simp [sobolevTerm]

/-- `L²` norm of the `L²` class attached to a real `L²` function. -/
theorem norm_potentialLp_sq {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    ‖Bridge.potentialLp u hu‖ ^ 2 = ∫ x, u x ^ 2 ∂torusMeasure d := by
  set U := Bridge.potentialLp u hu with hU
  have h1 : (‖U‖ ^ 2 : ℝ) = RCLike.re (inner ℂ U U) := by
    rw [inner_self_eq_norm_sq_to_K]
    change ‖U‖ ^ 2 = Complex.re ((‖U‖ : ℂ) ^ 2)
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h2 : inner ℂ U U = ∫ a, inner ℂ (U a) (U a) ∂torusMeasure d := L2.inner_def U U
  have h3 : ∀ᵐ a ∂torusMeasure d, (inner ℂ (U a) (U a) : ℂ) = ((u a ^ 2 : ℝ) : ℂ) := by
    filter_upwards [Bridge.potentialLp_ae u hu] with a ha
    rw [ha, inner_self_eq_norm_sq_to_K]
    change ((‖(u a : ℂ)‖ : ℂ)) ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← Complex.ofReal_pow, sq_abs]
  have h4 : ∫ a, ((u a ^ 2 : ℝ) : ℂ) ∂torusMeasure d = ((∫ a, u a ^ 2 ∂torusMeasure d : ℝ) : ℂ) :=
    integral_ofReal
  rw [h1, h2, integral_congr_ae h3]
  have h5 := congrArg Complex.re h4
  simpa using h5

/-- **Parseval base case.**  `‖u‖²_{H⁰} = ∫ u²`. -/
theorem sobolevNorm_zero_sq {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    sobolevNorm 0 u ^ 2 = ∫ x, u x ^ 2 ∂torusMeasure d := by
  have hnn : ∀ k : Frequency d, 0 ≤ sobolevTerm 0 u k := fun k => by
    rw [sobolevTerm_eq]; positivity
  have e1 : sobolevNorm 0 u ^ 2 = ∑' k : Frequency d, ‖fourierCoeff u k‖ ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt (tsum_nonneg hnn)]
    exact tsum_congr fun k => by simp [sobolevTerm]
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d (Bridge.potentialLp u hu))
  have e2 : ∑' k : Frequency d, ‖fourierCoeff u k‖ ^ 2 = ‖Bridge.potentialLp u hu‖ ^ 2 := by
    have h' : HasSum (fun k : Frequency d => ‖fourierCoeff u k‖ ^ 2) (‖Bridge.potentialLp u hu‖ ^ 2) := by
      simpa [Bridge.potentialLp_fourier] using h
    exact h'.tsum_eq
  rw [e1, e2, norm_potentialLp_sq]

end BecknerOnofri.V2.Onset

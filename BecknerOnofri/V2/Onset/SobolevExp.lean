module

public import BecknerOnofri.V2.Onset.SobolevAlgebra
public import BecknerOnofri.LocalElevenCore.WeightedExponentialRemainder

@[expose] public section

/-! # The exponential map on `H^s(𝕋^d)`, `s > d/2`

"`u ∈ H^{jd}` implies `e^u ∈ H^{jd}`" (proof of Proposition 5.24, via Corollary 2.6), in the
quantitative form `‖e^u‖_{H^s} ≤ exp(C_{d,s} ‖u‖_{H^s})`, where `C_{d,s} = sobolevAlgConst d s` is
the Banach-algebra constant of `SobolevAlgebra`.  The proof expands `e^u = ∑ u^n/n!` on the
Fourier side (`Legacy.BecknerOnofri.WienerFourier.exponentialCoefficients`), bounds the `n`-th
convolution power by `(C‖u‖)^n` and sums with Minkowski's inequality (`tsum_sq_tsum_le`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim
open Legacy.BecknerOnofri.WienerFourier (convolutionPower exponentialCoefficients)

theorem sobolevScale_zero {d : ℕ} (s : ℝ) : sobolevScale s (0 : Frequency d) = 1 := by
  simp [sobolevScale, frequencyLength]

theorem sobSq_convolutionPower_zero {d : ℕ} (s : ℝ) (a : Frequency d → ℂ) :
    sobSq s (convolutionPower a 0) = 1 := by
  classical
  unfold sobSq
  rw [tsum_eq_single (0 : Frequency d)]
  · simp [convolutionPower, sobolevScale_zero]
  · intro k hk
    simp [convolutionPower, hk]

theorem sq_rpow_half (A : ℝ≥0∞) : (A ^ 2) ^ (1 / 2 : ℝ) = A := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem sobSq_convolutionPower_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : Frequency d → ℂ) (n : ℕ) :
    sobSq s (convolutionPower a n) ≤
      ((4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s) * sobSq s a) ^ n := by
  induction n with
  | zero => simp [sobSq_convolutionPower_zero]
  | succ n ih =>
    have h : convolutionPower a (n + 1) = cconv (convolutionPower a n) a := by
      rw [← convolution_eq_cconv]; rfl
    rw [h, pow_succ]
    refine (sobSq_cconv_le_alg hs _ _).trans ?_
    calc _ ≤ (4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s) *
          (((4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s) * sobSq s a) ^ n) * sobSq s a := by
          gcongr
      _ = _ := by ring

/-- Sequence-level exponential estimate: with `X = (K ‖a‖²_s)^{1/2}`,
`‖exp_⋆ a‖²_s ≤ (∑ X^n / n!)²`. -/
theorem sobSq_exponentialCoefficients_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : Frequency d → ℂ) :
    sobSq s (exponentialCoefficients a) ≤
      (∑' n : ℕ, ENNReal.ofReal ((n.factorial : ℝ)⁻¹) *
        (((4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s) * sobSq s a) ^ (1 / 2 : ℝ)) ^ n) ^ 2 := by
  set K : ℝ≥0∞ := 4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s with hK
  set g : ℕ → Frequency d → ℝ≥0∞ := fun n k =>
    ENNReal.ofReal ((n.factorial : ℝ)⁻¹) * ENNReal.ofReal (sobolevScale s k * ‖convolutionPower a n k‖)
    with hg
  have hpt : ∀ k, ENNReal.ofReal (sobolevScale s k * ‖exponentialCoefficients a k‖) ≤
      ∑' n, g n k := by
    intro k
    have hw : 0 ≤ sobolevScale s k := (sobolevScale_pos s k).le
    rw [ENNReal.ofReal_mul hw, ofReal_norm]
    calc ENNReal.ofReal (sobolevScale s k) * ‖exponentialCoefficients a k‖ₑ
        ≤ ENNReal.ofReal (sobolevScale s k) *
            ∑' n : ℕ, ‖((n.factorial : ℂ)⁻¹ * convolutionPower a n k)‖ₑ := by
          gcongr
          exact enorm_tsum_le_tsum_enorm
      _ = ∑' n, g n k := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          simp only [hg]
          rw [ENNReal.ofReal_mul hw, ofReal_norm, enorm_mul, mul_left_comm]
          congr 1
          rw [← ofReal_norm]
          simp
  have hgk : ∀ n, ∑' k, g n k ^ 2 =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) ^ 2 * sobSq s (convolutionPower a n) := by
    intro n
    simp only [hg, mul_pow]
    rw [ENNReal.tsum_mul_left]
    rfl
  have hX : ∀ n, (∑' k, g n k ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) * ((K * sobSq s a) ^ (1 / 2 : ℝ)) ^ n := by
    intro n
    rw [hgk n, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]
    gcongr
    calc (sobSq s (convolutionPower a n)) ^ (1 / 2 : ℝ) ≤ ((K * sobSq s a) ^ n) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (sobSq_convolutionPower_le hs a n) (by norm_num)
      _ = ((K * sobSq s a) ^ (1 / 2 : ℝ)) ^ n := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            show ((n:ℝ) * (1 / 2)) = (1 / 2) * n by ring, ENNReal.rpow_mul, ENNReal.rpow_natCast]
  calc sobSq s (exponentialCoefficients a)
      = ∑' k, ENNReal.ofReal (sobolevScale s k * ‖exponentialCoefficients a k‖) ^ 2 := rfl
    _ ≤ ∑' k, (∑' n, g n k) ^ 2 := ENNReal.tsum_le_tsum fun k => by gcongr; exact hpt k
    _ ≤ (∑' n, (∑' k, g n k ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := tsum_sq_tsum_le g
    _ ≤ _ := by gcongr with n; exact hX n


section Space
open ContinuousGibbs ContinuousFirstShell

theorem tsum_ofReal_exp_series {x : ℝ} (hx : 0 ≤ x) :
    ∑' n : ℕ, ENNReal.ofReal ((n.factorial : ℝ)⁻¹) * ENNReal.ofReal x ^ n =
      ENNReal.ofReal (Real.exp x) := by
  have h := Real.summable_pow_div_factorial x
  have e : ∀ n : ℕ, ENNReal.ofReal ((n.factorial : ℝ)⁻¹) * ENNReal.ofReal x ^ n =
      ENNReal.ofReal (x ^ n / n.factorial) := fun n => by
    rw [← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_mul (by positivity), mul_comm, div_eq_mul_inv]
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h, Real.exp_eq_exp_ℝ,
    NormedSpace.exp_eq_tsum_div]

/-- **Exponential estimate in `H^s(𝕋^d)`, `s > d/2`** (continuous representatives):
`‖e^u‖_{H^s} ≤ exp(C_{d,s} ‖u‖_{H^s})`. -/
theorem sobolev_exp_space {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) (u : Space d)
    (hu : InSobolev s u) :
    InSobolev s (⇑(exponential u)) ∧
      sobolevNorm s (⇑(exponential u)) ≤ Real.exp (sobolevAlgConst d s * sobolevNorm s (⇑u)) := by
  have hs0 : 0 ≤ s := by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set x : ℝ := sobolevAlgConst d s * sobolevNorm s (⇑u) with hxdef
  have hx0 : 0 ≤ x := mul_nonneg (sobolevAlgConst_nonneg d s) (sobolevNorm_nonneg' _ _)
  have hqfin := ((inSobolev_iff (s := s) (⇑u)).mp hu).2
  have hq : sobSq s (fourierCoeff (⇑u)) = ENNReal.ofReal (sobolevNorm s (⇑u) ^ 2) := by
    rw [sobolevNorm_sq_eq hu, ENNReal.ofReal_toReal hqfin]
  have hcoef : fourierCoeff (⇑(exponential u)) = exponentialCoefficients (fourierCoeff (⇑u)) := by
    rw [fourierCoeff_eq_coefficient, fourierCoeff_eq_coefficient]
    funext k
    exact LocalEleven.WeightedExponentialRemainder.coefficient_exponential u
      (summable_coefficient hd hs hu) k
  have hK : (4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s) * sobSq s (fourierCoeff (⇑u)) =
      ENNReal.ofReal (x ^ 2) := by
    rw [alg_eq hd hs, hq, ← ENNReal.ofReal_mul (sq_nonneg _), hxdef, mul_pow]
  have hbound : sobSq s (fourierCoeff (⇑(exponential u))) ≤ ENNReal.ofReal (Real.exp x) ^ 2 := by
    rw [hcoef]
    refine (sobSq_exponentialCoefficients_le hs0 _).trans ?_
    rw [hK, ENNReal.ofReal_pow hx0, sq_rpow_half, tsum_ofReal_exp_series hx0]
  have hfin : sobSq s (fourierCoeff (⇑(exponential u))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hbound
  have hmem : InSobolev s (⇑(exponential u)) :=
    (inSobolev_iff _).mpr ⟨ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ (exponential u), hfin⟩
  refine ⟨hmem, ?_⟩
  have h2 : sobolevNorm s (⇑(exponential u)) ^ 2 ≤ Real.exp x ^ 2 := by
    rw [sobolevNorm_sq_eq hmem]
    have := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hbound
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos x).le] at this
  exact (pow_le_pow_iff_left₀ (sobolevNorm_nonneg' _ _) (Real.exp_pos x).le two_ne_zero).mp h2

end Space

end BecknerOnofri.V2.Onset

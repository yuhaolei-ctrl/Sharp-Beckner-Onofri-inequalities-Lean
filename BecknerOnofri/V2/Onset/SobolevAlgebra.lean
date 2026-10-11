module

public import BecknerOnofri.GeneralSobolevEmbedding
public import BecknerOnofri.LocalElevenCore.WienerProductCore
public import BecknerOnofri.OnsetRaw
public import BecknerOnofri.V2.Onset.YoungSeq

@[expose] public section

/-! # The Banach-algebra property of `H^s(𝕋^d)`, `s > d/2`

Used in the manuscript in the proof of Proposition 5.24 ("`H^{jd}` is a Banach algebra embedded in
`L^∞`", `eq:section5-onset-uniform-smoothness`, via Corollary 2.6) and in the setup of the
Lyapunov-Schmidt reduction ("analyticity follows from the Banach-algebra property of `H^s`").

The repository vocabulary is `InSobolev s u`, `sobolevNorm s u` (`BecknerOnofri.Statement`), with
`sobolevTerm s u k = (1 + (2π|k|)²)^s ‖û(k)‖²`.  The estimate is proved at the level of
Fourier coefficient sequences in `ℝ≥0∞` (no summability bookkeeping), then transferred to
functions through the Fourier coefficient of a product of continuous functions with absolutely
summable coefficients (`LocalEleven.WienerAlgebraBounds.coefficient_product`).

Main results:
* `sobSq_cconv_le` : `‖a * b‖²_{s} ≤ 4 · 4^s · Θ_s · ‖a‖²_{s} ‖b‖²_{s}` for coefficient sequences;
* `sobolev_mul` : for `s > d/2`, the product of two `H^s` functions is in `H^s` and
  `‖uv‖_{H^s} ≤ sobolevAlgConst hd hs · ‖u‖_{H^s} ‖v‖_{H^s}`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

/-! ## Weights -/

theorem frequencyLength_eq_norm {d : ℕ} (k : Frequency d) :
    frequencyLength k = ‖(WithLp.toLp 2 (fun i => (k i : ℝ)) : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [frequencyLength]

theorem frequencyLength_sub_le {d : ℕ} (k l : Frequency d) :
    frequencyLength k ≤ frequencyLength (k - l) + frequencyLength l := by
  rw [frequencyLength_eq_norm, frequencyLength_eq_norm, frequencyLength_eq_norm]
  have : (WithLp.toLp 2 (fun i => (k i : ℝ)) : EuclideanSpace ℝ (Fin d)) =
      WithLp.toLp 2 (fun i => ((k - l) i : ℝ)) + WithLp.toLp 2 (fun i => (l i : ℝ)) := by
    ext i; simp
  rw [this]
  exact norm_add_le _ _

/-- Peetre-type inequality `w(k) ≤ 2^s (w(k - l) + w(l))` for the weight `(1 + (2π|k|)²)^{s/2}`. -/
theorem sobolevScale_le_add {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (k l : Frequency d) :
    sobolevScale s k ≤ (2:ℝ) ^ s * (sobolevScale s (k - l) + sobolevScale s l) := by
  have key : ∀ (c x y : ℝ), 0 ≤ c → 0 ≤ x → 0 ≤ y → c ≤ x + y → x ≤ y →
      (1 + (2 * Real.pi * c) ^ 2) ^ (s / 2) ≤ (2:ℝ) ^ s * (1 + (2 * Real.pi * y) ^ 2) ^ (s / 2) := by
    intro c x y hc hx hy hcxy hxy
    have h1 : 1 + (2 * Real.pi * c) ^ 2 ≤ 4 * (1 + (2 * Real.pi * y) ^ 2) := by
      have : 2 * Real.pi * c ≤ 2 * (2 * Real.pi * y) := by nlinarith [Real.pi_pos]
      have h0 : 0 ≤ 2 * Real.pi * c := by positivity
      nlinarith [sq_nonneg (2 * Real.pi * y)]
    calc (1 + (2 * Real.pi * c) ^ 2) ^ (s / 2) ≤ (4 * (1 + (2 * Real.pi * y) ^ 2)) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = (4:ℝ) ^ (s / 2) * (1 + (2 * Real.pi * y) ^ 2) ^ (s / 2) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ = (2:ℝ) ^ s * (1 + (2 * Real.pi * y) ^ 2) ^ (s / 2) := by
          congr 1
          rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          congr 1; ring
  have hk := frequencyLength_sub_le k l
  have h1 : 0 ≤ frequencyLength (k - l) := Real.sqrt_nonneg _
  have h2 : 0 ≤ frequencyLength l := Real.sqrt_nonneg _
  have h3 : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  have hp : 0 ≤ (2:ℝ) ^ s := by positivity
  unfold sobolevScale
  rcases le_total (frequencyLength (k - l)) (frequencyLength l) with h | h
  · have : 0 ≤ (1 + (2 * Real.pi * frequencyLength (k - l)) ^ 2) ^ (s / 2) := by positivity
    nlinarith [key _ _ _ h3 h1 h2 hk h]
  · have : 0 ≤ (1 + (2 * Real.pi * frequencyLength l) ^ 2) ^ (s / 2) := by positivity
    nlinarith [key _ _ _ h3 h2 h1 (by linarith) h]

theorem add_sq_le_two_mul (X Y : ℝ≥0∞) : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by
  by_cases hX : X = ⊤
  · simp [hX]
  by_cases hY : Y = ⊤
  · simp [hY]
  lift X to NNReal using hX
  lift Y to NNReal using hY
  have h : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by
    have := two_mul_le_add_sq X Y
    calc (X + Y) ^ 2 = X ^ 2 + 2 * X * Y + Y ^ 2 := by ring
      _ ≤ X ^ 2 + (X ^ 2 + Y ^ 2) + Y ^ 2 := by gcongr
      _ = 2 * (X ^ 2 + Y ^ 2) := by ring
  exact_mod_cast h

/-! ## The weighted estimate for coefficient sequences -/

/-- Weighted squared `ℓ²` size `∑ (w_k ‖a_k‖)²` of a Fourier-coefficient sequence, with
`w_k = (1 + (2π|k|)²)^{s/2}`; for `a = û` it equals `‖u‖²_{H^s}` (`sobSq_fourierCoeff`). -/
def sobSq {d : ℕ} (s : ℝ) (a : Frequency d → ℂ) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (sobolevScale s k * ‖a k‖) ^ 2

/-- The `ℓ¹` size `∑ ‖a_k‖` (Wiener-algebra size). -/
def l1E {d : ℕ} (a : Frequency d → ℂ) : ℝ≥0∞ := ∑' k, ENNReal.ofReal ‖a k‖

/-- Convolution `(a ⋆ b)(k) = ∑_l a(k - l) b(l)` of Fourier coefficient sequences. -/
def cconv {d : ℕ} (a b : Frequency d → ℂ) (k : Frequency d) : ℂ := ∑' l, a (k - l) * b l

/-- `Θ_s = ∑_k (1 + (2π|k|)²)^{-s}`, finite exactly when `s > d/2`. -/
def Theta (d : ℕ) (s : ℝ) : ℝ≥0∞ := ∑' k : Frequency d, ENNReal.ofReal ((sobolevScale s k)⁻¹ ^ 2)

theorem ofReal_cconv_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a b : Frequency d → ℂ) (k : Frequency d) :
    ENNReal.ofReal (sobolevScale s k * ‖cconv a b k‖) ≤ ENNReal.ofReal ((2:ℝ) ^ s) *
      (convE (fun j => ENNReal.ofReal (sobolevScale s j * ‖a j‖)) (fun j => ENNReal.ofReal ‖b j‖) k +
       convE (fun j => ENNReal.ofReal ‖a j‖) (fun j => ENNReal.ofReal (sobolevScale s j * ‖b j‖)) k) := by
  have hw : ∀ j : Frequency d, 0 ≤ sobolevScale s j := fun j => (sobolevScale_pos s j).le
  rw [ENNReal.ofReal_mul (hw k), ofReal_norm]
  calc ENNReal.ofReal (sobolevScale s k) * ‖cconv a b k‖ₑ
      ≤ ENNReal.ofReal (sobolevScale s k) * ∑' l, ‖a (k - l)‖ₑ * ‖b l‖ₑ := by
        gcongr
        refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
        exact tsum_congr fun l => enorm_mul _ _
    _ = ∑' l, ENNReal.ofReal (sobolevScale s k) * (‖a (k - l)‖ₑ * ‖b l‖ₑ) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' l, ENNReal.ofReal ((2:ℝ) ^ s) *
          (ENNReal.ofReal (sobolevScale s (k - l) * ‖a (k - l)‖) * ENNReal.ofReal ‖b l‖ +
           ENNReal.ofReal ‖a (k - l)‖ * ENNReal.ofReal (sobolevScale s l * ‖b l‖)) := by
        refine ENNReal.tsum_le_tsum fun l => ?_
        have h1 : ENNReal.ofReal (sobolevScale s k) ≤ ENNReal.ofReal ((2:ℝ) ^ s) *
            (ENNReal.ofReal (sobolevScale s (k - l)) + ENNReal.ofReal (sobolevScale s l)) := by
          rw [← ENNReal.ofReal_add (hw _) (hw _), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (sobolevScale_le_add hs k l)
        calc ENNReal.ofReal (sobolevScale s k) * (‖a (k - l)‖ₑ * ‖b l‖ₑ)
            ≤ (ENNReal.ofReal ((2:ℝ) ^ s) *
            (ENNReal.ofReal (sobolevScale s (k - l)) + ENNReal.ofReal (sobolevScale s l))) *
              (‖a (k - l)‖ₑ * ‖b l‖ₑ) := by gcongr
          _ = _ := by
            rw [ENNReal.ofReal_mul (hw _), ENNReal.ofReal_mul (hw _), ofReal_norm, ofReal_norm]
            ring
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        rfl

/-- Convolution estimate with `ℓ¹` factors. -/
theorem sobSq_cconv_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a b : Frequency d → ℂ) :
    sobSq s (cconv a b) ≤ 2 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 *
      (sobSq s a * l1E b ^ 2 + l1E a ^ 2 * sobSq s b) := by
  set K0 := ENNReal.ofReal ((2:ℝ) ^ s) with hK0
  set A : Frequency d → ℝ≥0∞ := fun j => ENNReal.ofReal (sobolevScale s j * ‖a j‖) with hA
  set B : Frequency d → ℝ≥0∞ := fun j => ENNReal.ofReal (sobolevScale s j * ‖b j‖) with hB
  set α : Frequency d → ℝ≥0∞ := fun j => ENNReal.ofReal ‖a j‖ with hα
  set β : Frequency d → ℝ≥0∞ := fun j => ENNReal.ofReal ‖b j‖ with hβ
  have hX : ∑' k, convE A β k ^ 2 ≤ sobSq s a * l1E b ^ 2 := tsum_convE_sq_le A β
  have hY : ∑' k, convE α B k ^ 2 ≤ l1E a ^ 2 * sobSq s b := by
    simp only [convE_comm α B]
    have := tsum_convE_sq_le B α
    rw [mul_comm]
    exact this
  calc sobSq s (cconv a b) = ∑' k, ENNReal.ofReal (sobolevScale s k * ‖cconv a b k‖) ^ 2 := rfl
    _ ≤ ∑' k, (K0 * (convE A β k + convE α B k)) ^ 2 :=
        ENNReal.tsum_le_tsum fun k => by gcongr; exact ofReal_cconv_le hs a b k
    _ ≤ ∑' k, K0 ^ 2 * (2 * (convE A β k ^ 2 + convE α B k ^ 2)) :=
        ENNReal.tsum_le_tsum fun k => by
          rw [mul_pow]; gcongr; exact add_sq_le_two_mul _ _
    _ = 2 * K0 ^ 2 * (∑' k, convE A β k ^ 2 + ∑' k, convE α B k ^ 2) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun k => ?_
        ring
    _ ≤ _ := by gcongr

theorem l1E_sq_le {d : ℕ} (s : ℝ) (a : Frequency d → ℂ) :
    l1E a ^ 2 ≤ Theta d s * sobSq s a := by
  have h := tsum_mul_sq_le (fun k : Frequency d => ENNReal.ofReal (sobolevScale s k ^ 2 * ‖a k‖))
    (fun k => ENNReal.ofReal ((sobolevScale s k)⁻¹ ^ 2))
  have hw : ∀ k : Frequency d, sobolevScale s k ≠ 0 := fun k => (sobolevScale_pos s k).ne'
  have e1 : ∀ k : Frequency d, ENNReal.ofReal (sobolevScale s k ^ 2 * ‖a k‖) *
      ENNReal.ofReal ((sobolevScale s k)⁻¹ ^ 2) = ENNReal.ofReal ‖a k‖ := fun k => by
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ sobolevScale s k ^ 2 * ‖a k‖)]
    congr 1
    field_simp [hw k]
  have e2 : ∀ k : Frequency d, ENNReal.ofReal (sobolevScale s k ^ 2 * ‖a k‖) ^ 2 *
      ENNReal.ofReal ((sobolevScale s k)⁻¹ ^ 2) = ENNReal.ofReal (sobolevScale s k * ‖a k‖) ^ 2 :=
    fun k => by
    have hp : 0 ≤ sobolevScale s k ^ 2 * ‖a k‖ := by positivity
    rw [← ENNReal.ofReal_pow hp, ← ENNReal.ofReal_mul (pow_nonneg hp 2),
      ← ENNReal.ofReal_pow (mul_nonneg (sobolevScale_pos s k).le (norm_nonneg _))]
    congr 1
    field_simp [hw k]
  simp only [e1, e2] at h
  exact h

/-- The algebra estimate for coefficient sequences, in squared form. -/
theorem sobSq_cconv_le_alg {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a b : Frequency d → ℂ) :
    sobSq s (cconv a b) ≤ (4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s) * sobSq s a * sobSq s b := by
  refine (sobSq_cconv_le hs a b).trans ?_
  have h1 : l1E b ^ 2 ≤ Theta d s * sobSq s b := l1E_sq_le s b
  have h2 : l1E a ^ 2 ≤ Theta d s * sobSq s a := l1E_sq_le s a
  calc 2 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * (sobSq s a * l1E b ^ 2 + l1E a ^ 2 * sobSq s b)
      ≤ 2 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 *
        (sobSq s a * (Theta d s * sobSq s b) + (Theta d s * sobSq s a) * sobSq s b) := by gcongr
    _ = _ := by ring


/-! ## Transfer to functions -/

theorem summable_inverse_scale_sq {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) :
    Summable (fun k : Frequency d => ((sobolevScale s k)⁻¹) ^ 2) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hp : (1/2:ℝ) < s / d := (lt_div_iff₀ hd').mpr (by linarith)
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (SobolevEmbedding.inverse_scale_square_le_product hd hs)
    (SobolevEmbedding.summable_productWeight d hp)

/-- `Θ_s = ∑_k (1 + (2π|k|)²)^{-s}` as a real number (summable iff `s > d/2`). -/
def thetaR (d : ℕ) (s : ℝ) : ℝ := ∑' k : Frequency d, ((sobolevScale s k)⁻¹) ^ 2

theorem thetaR_nonneg (d : ℕ) (s : ℝ) : 0 ≤ thetaR d s :=
  tsum_nonneg fun _ => sq_nonneg _

theorem Theta_eq {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) :
    Theta d s = ENNReal.ofReal (thetaR d s) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (summable_inverse_scale_sq hd hs)).symm

/-- The Banach-algebra constant of `H^s(𝕋^d)`, `s > d/2`: `2^{s+1} Θ_s^{1/2}`. -/
def sobolevAlgConst (d : ℕ) (s : ℝ) : ℝ := (2:ℝ) ^ (s + 1) * Real.sqrt (thetaR d s)

theorem sobolevAlgConst_nonneg (d : ℕ) (s : ℝ) : 0 ≤ sobolevAlgConst d s :=
  mul_nonneg (by positivity) (Real.sqrt_nonneg _)

theorem alg_eq {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) :
    4 * ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * Theta d s = ENNReal.ofReal (sobolevAlgConst d s ^ 2) := by
  rw [Theta_eq hd hs, ← ENNReal.ofReal_pow (by positivity)]
  have h4 : (4:ℝ≥0∞) = ENNReal.ofReal 4 := by simp
  rw [h4, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [sobolevAlgConst, mul_pow, Real.sq_sqrt (thetaR_nonneg d s), Real.rpow_add (by norm_num),
    Real.rpow_one]
  ring

/-- `sobolevTerm` in terms of the weight `w_k`. -/
theorem sobolevTerm_eq {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (k : Frequency d) :
    sobolevTerm s u k = (sobolevScale s k * ‖fourierCoeff u k‖) ^ 2 := by
  rw [mul_pow, sobolevScale_sq]; rfl

theorem tsum_ofReal_sobolevTerm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) :
    ∑' k, ENNReal.ofReal (sobolevTerm s u k) = sobSq s (fourierCoeff u) := by
  unfold sobSq
  refine tsum_congr fun k => ?_
  rw [sobolevTerm_eq, ENNReal.ofReal_pow (mul_nonneg (sobolevScale_pos s k).le (norm_nonneg _))]

theorem summable_sobolevTerm_iff {d : ℕ} (s : ℝ) (u : Torus d → ℝ) :
    Summable (sobolevTerm s u) ↔ sobSq s (fourierCoeff u) ≠ ⊤ := by
  rw [← tsum_ofReal_sobolevTerm]
  constructor
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by rw [sobolevTerm_eq]; positivity) h]
    exact ENNReal.ofReal_ne_top
  · intro h
    have := ENNReal.summable_toReal h
    refine this.congr fun k => ?_
    rw [ENNReal.toReal_ofReal (by rw [sobolevTerm_eq]; positivity)]

theorem sobolevNorm_sq_eq {d : ℕ} {s : ℝ} {u : Torus d → ℝ} (hu : InSobolev s u) :
    sobolevNorm s u ^ 2 = (sobSq s (fourierCoeff u)).toReal := by
  unfold sobolevNorm
  rw [Real.sq_sqrt (tsum_nonneg fun _ => by rw [sobolevTerm_eq]; positivity), ← tsum_ofReal_sobolevTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => by rw [sobolevTerm_eq]; positivity) hu.2,
    ENNReal.toReal_ofReal (tsum_nonneg fun _ => by rw [sobolevTerm_eq]; positivity)]

theorem inSobolev_iff {d : ℕ} {s : ℝ} (u : Torus d → ℝ) :
    InSobolev s u ↔ MemLp u 2 (torusMeasure d) ∧ sobSq s (fourierCoeff u) ≠ ⊤ := by
  unfold InSobolev
  rw [summable_sobolevTerm_iff]

/-- The `ℓ¹` size of the Fourier coefficients of an `H^s` function, `s > d/2`, is finite. -/
theorem l1E_ne_top {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) {u : Torus d → ℝ}
    (hu : InSobolev s u) : l1E (fourierCoeff u) ≠ ⊤ := by
  have := SobolevEmbedding.fourier_summable hd hs u hu
  unfold l1E
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) this]
  exact ENNReal.ofReal_ne_top

/-! ## The product of continuous functions -/

theorem convolution_eq_cconv {d : ℕ} (a b : Frequency d → ℂ) :
    Legacy.BecknerOnofri.WienerFourier.convolution a b = cconv a b := by
  funext k
  unfold Legacy.BecknerOnofri.WienerFourier.convolution Legacy.BecknerOnofri.WienerFourier.grouped
    cconv
  let e : Frequency d ≃ ((fun p : Frequency d × Frequency d => p.1 + p.2) ⁻¹' {k}) :=
    { toFun := fun l => ⟨(k - l, l), by simp⟩
      invFun := fun p => p.1.2
      left_inv := fun l => rfl
      right_inv := fun p => by
        apply Subtype.ext
        have hp : p.1.1 + p.1.2 = k := p.2
        apply Prod.ext
        · exact sub_eq_of_eq_add hp.symm
        · rfl }
  rw [← e.tsum_eq]
  rfl


section Space
open ContinuousGibbs ContinuousFirstShell

theorem sobolevNorm_nonneg' {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : 0 ≤ sobolevNorm s u :=
  Real.sqrt_nonneg _

theorem fourierCoeff_eq_coefficient {d : ℕ} (u : Space d) :
    fourierCoeff (⇑u) = fun k => coefficient k u :=
  funext fun k => (coefficient_eq_fourierCoeff k u).symm

theorem summable_coefficient {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) {u : Space d}
    (hu : InSobolev s u) : Summable (fun k => ‖coefficient k u‖) :=
  (SobolevEmbedding.fourier_summable hd hs u hu).congr fun k => by
    rw [coefficient_eq_fourierCoeff]

/-- **Banach-algebra property of `H^s(𝕋^d)`, `s > d/2`** (continuous representatives). -/
theorem sobolev_mul_space {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) (u v : Space d)
    (hu : InSobolev s u) (hv : InSobolev s v) :
    InSobolev s (⇑(u * v)) ∧
      sobolevNorm s (⇑(u * v)) ≤ sobolevAlgConst d s * sobolevNorm s (⇑u) * sobolevNorm s (⇑v) := by
  have hs0 : 0 ≤ s := by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hcoef : fourierCoeff (⇑(u * v)) = cconv (fourierCoeff (⇑u)) (fourierCoeff (⇑v)) := by
    rw [fourierCoeff_eq_coefficient, fourierCoeff_eq_coefficient, fourierCoeff_eq_coefficient]
    funext k
    rw [LocalEleven.WienerAlgebraBounds.coefficient_product u v (summable_coefficient hd hs hu)
      (summable_coefficient hd hs hv) k, convolution_eq_cconv]
  have hbound : sobSq s (fourierCoeff (⇑(u * v))) ≤
      ENNReal.ofReal (sobolevAlgConst d s ^ 2) * sobSq s (fourierCoeff (⇑u)) *
        sobSq s (fourierCoeff (⇑v)) := by
    rw [hcoef, ← alg_eq hd hs]
    exact sobSq_cconv_le_alg hs0 _ _
  have hu' := ((inSobolev_iff (s := s) (⇑u)).mp hu).2
  have hv' := ((inSobolev_iff (s := s) (⇑v)).mp hv).2
  have hfin : sobSq s (fourierCoeff (⇑(u * v))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu') hv')
      hbound
  have hmem : InSobolev s (⇑(u * v)) :=
    (inSobolev_iff _).mpr ⟨ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ (u * v), hfin⟩
  refine ⟨hmem, ?_⟩
  have h2 : sobolevNorm s (⇑(u * v)) ^ 2 ≤
      (sobolevAlgConst d s * sobolevNorm s (⇑u) * sobolevNorm s (⇑v)) ^ 2 := by
    rw [sobolevNorm_sq_eq hmem, mul_pow, mul_pow, sobolevNorm_sq_eq hu, sobolevNorm_sq_eq hv]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu') hv')
      hbound
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at this
  exact (pow_le_pow_iff_left₀ (sobolevNorm_nonneg' _ _)
    (mul_nonneg (mul_nonneg (sobolevAlgConst_nonneg d s) (sobolevNorm_nonneg' _ _))
      (sobolevNorm_nonneg' _ _)) (two_ne_zero)).mp h2


/-- **Banach-algebra property of `H^s(𝕋^d)`, `s > d/2`** for raw functions: the product of two
`H^s` functions is in `H^s`, with `‖uv‖_{H^s} ≤ C_{d,s} ‖u‖_{H^s}‖v‖_{H^s}`. -/
theorem sobolev_mul {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d : ℝ) / 2 < s) (u v : Torus d → ℝ)
    (hu : InSobolev s u) (hv : InSobolev s v) :
    InSobolev s (fun x => u x * v x) ∧
      sobolevNorm s (fun x => u x * v x) ≤
        sobolevAlgConst d s * sobolevNorm s u * sobolevNorm s v := by
  obtain ⟨u', hu1, hu2, -⟩ := SobolevEmbedding.exists_continuous_representative hd hs u hu
  obtain ⟨v', hv1, hv2, -⟩ := SobolevEmbedding.exists_continuous_representative hd hs v hv
  have hae : (fun x => u x * v x) =ᵐ[torusMeasure d] ⇑(u' * v') := by
    filter_upwards [hu1, hv1] with x hx hy
    simp [hx, hy]
  have h := sobolev_mul_space hd hs u' v' hu2 hv2
  rw [OnsetRaw.inSobolev_congr_ae hae, OnsetRaw.sobolevNorm_congr_ae hae,
    ← OnsetRaw.sobolevNorm_congr_ae hu1, ← OnsetRaw.sobolevNorm_congr_ae hv1]
  exact h

end Space

end BecknerOnofri.V2.Onset

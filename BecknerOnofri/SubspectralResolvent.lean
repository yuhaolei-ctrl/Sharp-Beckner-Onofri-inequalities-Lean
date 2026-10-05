module

public import BecknerOnofri.GreenCritical
public import BecknerOnofri.GraphWienerBounds

@[expose] public section

/-! The full Green linearization below the first eigenvalue. The Fourier
resolvent is bounded by (1-mu)^{-1}; Green regularization then constructs
its inverse on the real continuous-function Banach space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace BecknerOnofri.HighDim.SubspectralResolvent
open ContinuousGibbs ContinuousFirstShell

def symbol {d : ℕ} (μ : ℝ) (k : Frequency d) : ℝ :=
  if k = 0 then 1 else 1-μ/frequencyLength k^d

lemma symbol_bounds {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (k : Frequency d) :
    1-μ ≤ symbol μ k ∧ symbol μ k ≤ 1 := by
  by_cases hk : k = 0
  · simp only [symbol, if_pos hk]; constructor <;> linarith
  · rw [symbol, if_neg hk]
    have hl := GreenCritical.nonzero_eigenvalue_ge_one (⟨k,hk⟩ : NonzeroFrequency d)
    have hp : 0 < frequencyLength k^d := lt_of_lt_of_le zero_lt_one hl
    have hd : μ/frequencyLength k^d ≤ μ := (div_le_iff₀ hp).mpr (by nlinarith)
    constructor <;> linarith [div_nonneg hμ hp.le]

lemma symbol_pos {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (k : Frequency d) :
    0 < symbol μ k := lt_of_lt_of_le (sub_pos.mpr hμ1) (symbol_bounds hμ hμ1 k).1

lemma symbol_inv_bound {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (k : Frequency d) :
    ‖((symbol μ k)⁻¹:ℝ)‖ ≤ (1-μ)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (symbol_pos hμ hμ1 k))]
  exact inv_anti₀ (sub_pos.mpr hμ1) (symbol_bounds hμ hμ1 k).1

def inverseLp {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (a : FourierL2 d) : FourierL2 d :=
  ⟨fun k => (((symbol μ k)⁻¹:ℝ):ℂ)*a k,
    ((lp.memℓp a).norm.const_mul ((1-μ)⁻¹)).mono (fun k => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (symbol_inv_bound hμ hμ1 k) (norm_nonneg _))⟩

lemma inverseLp_bound {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (a : FourierL2 d) :
    ‖inverseLp hμ hμ1 a‖ ≤ (1-μ)⁻¹*‖a‖ := by
  have hR : ‖((1-μ)⁻¹:ℝ)‖ = (1-μ)⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr (sub_pos.mpr hμ1).le)
  have h : ‖inverseLp hμ hμ1 a‖ ≤ ‖((1-μ)⁻¹:ℝ) • a‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro k
    change ‖(((symbol μ k)⁻¹:ℝ):ℂ)*a k‖ ≤ ‖((1-μ)⁻¹:ℝ) • a k‖
    rw [norm_mul, Complex.norm_real, norm_smul, hR]
    exact mul_le_mul_of_nonneg_right (symbol_inv_bound hμ hμ1 k) (norm_nonneg _)
  simpa only [norm_smul, hR] using h

def inverseLpLinear {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) : FourierL2 d →ₗ[ℂ] FourierL2 d where
  toFun := inverseLp hμ hμ1
  map_add' a b := by
    apply lp.ext; funext k
    exact mul_add _ (a k) (b k)
  map_smul' c a := by
    apply lp.ext; funext k
    change (((symbol μ k)⁻¹:ℝ):ℂ)*(c*a k) = c*((((symbol μ k)⁻¹:ℝ):ℂ)*a k)
    ring

def inverseLpCLM {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) : FourierL2 d →L[ℂ] FourierL2 d :=
  (inverseLpLinear hμ hμ1).mkContinuous ((1-μ)⁻¹) (inverseLp_bound hμ hμ1)

lemma inverseLp_conjugate {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) :
    ConjugateSymmetric (inverseLp hμ hμ1 a : Frequency d → ℂ) := by
  intro k
  change (((symbol μ (-k))⁻¹:ℝ):ℂ)*a (-k) = conj ((((symbol μ k)⁻¹:ℝ):ℂ)*a k)
  rw [map_mul, Complex.conj_ofReal, ha k]
  simp only [symbol, neg_eq_zero, frequencyLength_neg]

def realPart {d : ℕ} : C(Torus d,ℂ) →L[ℝ] Space d :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp [Complex.real_smul] }
    1 (fun f => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x =>
        (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm x)))

def inverse {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) : Space d →L[ℝ] Space d :=
  ContinuousLinearMap.id ℝ (Space d) + μ • realPart.comp
    (((greenLiftComplex d).comp (inverseLpCLM hμ hμ1)).restrictScalars ℝ |>.comp (continuousFourier d))

lemma inverse_fourier {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1)
    (u : Space d) (k : Frequency d) :
    coefficient k (inverse hμ hμ1 u) = (((symbol μ k)⁻¹:ℝ):ℂ)*coefficient k u := by
  let a := inverseLp hμ hμ1 (continuousFourier d u)
  have ha : ConjugateSymmetric (a : Frequency d → ℂ) :=
    inverseLp_conjugate hμ hμ1 _ (fun k => coefficient_neg k u)
  have he (x : Torus d) : ((realPart (greenLiftComplex d a) x:ℝ):ℂ) = greenLiftComplex d a x := by
    apply Complex.ext
    · rfl
    · exact (greenLiftComplex_real hd a ha x).symm
  have hcoeff : coefficient k (realPart (greenLiftComplex d a)) =
      ((if k=0 then 0 else 1/frequencyLength k^d:ℝ):ℂ)*a k := by
    rw [coefficient_eq_fourierCoeff]
    have hh := greenLiftComplex_fourier hd a k
    convert hh using 1
    unfold fourierCoeff UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp only; rw [he]; rfl)
  change coefficient k (u + μ • realPart (greenLiftComplex d a)) = _
  rw [map_add, map_smul, hcoeff]
  change coefficient k u + μ • (((if k=0 then 0 else 1/frequencyLength k^d:ℝ):ℂ)*
    ((((symbol μ k)⁻¹:ℝ):ℂ)*coefficient k u)) = _
  by_cases hk : k = 0
  · simp [symbol, hk]
  · have hl : frequencyLength k^d ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (GreenCritical.nonzero_eigenvalue_ge_one (⟨k,hk⟩ : NonzeroFrequency d))).ne'
    have hs : symbol μ k ≠ 0 := (symbol_pos hμ hμ1 k).ne'
    simp only [if_neg hk, Complex.real_smul]
    have heq : 1 + μ*(1/frequencyLength k^d)*(symbol μ k)⁻¹ = (symbol μ k)⁻¹ := by
      rw [show μ*(1/frequencyLength k^d) = 1-symbol μ k by simp [symbol, hk, div_eq_mul_inv]]
      field_simp
      <;> ring
    have heqC := congrArg (fun r : ℝ => (r:ℂ)) heq
    push_cast at heqC ⊢
    linear_combination heqC * coefficient k u

def forward (d : ℕ) (μ : ℝ) : Space d →L[ℝ] Space d :=
  ContinuousLinearMap.id ℝ (Space d) - μ • greenContinuous d

lemma forward_fourier {d : ℕ} (hd : 0 < d) (μ : ℝ) (u : Space d) (k : Frequency d) :
    coefficient k (forward d μ u) = (symbol μ k:ℂ)*coefficient k u := by
  change coefficient k (u-μ • greenContinuous d u) = _
  rw [map_sub, map_smul, coefficient_green hd]
  by_cases hk : k = 0
  · simp [symbol, hk]
  · simp only [symbol, if_neg hk, Complex.real_smul]
    push_cast
    ring

lemma inverse_left {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Space d) :
    inverse hμ hμ1 (forward d μ u) = u := by
  apply coefficient_ext
  intro k
  rw [inverse_fourier hd, forward_fourier hd]
  have hs : (symbol μ k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (symbol_pos hμ hμ1 k).ne'
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

lemma inverse_right {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Space d) :
    forward d μ (inverse hμ hμ1 u) = u := by
  apply coefficient_ext
  intro k
  rw [forward_fourier hd, inverse_fourier hd]
  have hs : (symbol μ k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (symbol_pos hμ hμ1 k).ne'
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

def equivalence {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) : Space d ≃L[ℝ] Space d where
  toLinearEquiv :=
    { toFun := forward d μ
      invFun := inverse hμ hμ1
      left_inv := inverse_left hd hμ hμ1
      right_inv := inverse_right hd hμ hμ1
      map_add' := map_add _
      map_smul' := map_smul _ }
  continuous_toFun := (forward d μ).continuous
  continuous_invFun := (inverse hμ hμ1).continuous

lemma equivalence_toCLM {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    (equivalence hd hμ hμ1 : Space d →L[ℝ] Space d) =
      ContinuousLinearMap.id ℝ (Space d)-μ • greenContinuous d := rfl

#print axioms equivalence
end BecknerOnofri.HighDim.SubspectralResolvent

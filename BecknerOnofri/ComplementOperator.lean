module

public import BecknerOnofri.ComplementGap
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

@[expose] public section

/-! A genuine bounded continuous inverse on the closed first-shell complement
of Fourier ℓ². No operator norm or inverse is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim

abbrev FourierL2 (d : ℕ) := lp (fun _ : Frequency d => ℂ) 2

/-- Closed Fourier Hilbert subspace orthogonal to constants and all first modes. -/
def lpComplement (d : ℕ) : Submodule ℂ (FourierL2 d) where
  carrier := {a | ComplementSupported (a : Frequency d → ℂ)}
  zero_mem' := by intro k hk; rfl
  add_mem' := by intro a b ha hb k hk; simp only [lp.coeFn_add, Pi.add_apply, ha k hk, hb k hk, add_zero]
  smul_mem' := by intro c a ha k hk; simp only [lp.coeFn_smul, Pi.smul_apply, ha k hk, smul_zero]

theorem lpComplement_isClosed (d : ℕ) : IsClosed (lpComplement d : Set (FourierL2 d)) := by
  change IsClosed {a : FourierL2 d | ∀ k, ¬ ComplementFrequency k → a k = 0}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro hk
  exact isClosed_eq (lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 k).continuous continuous_const

instance lpComplement_completeSpace (d : ℕ) : CompleteSpace (lpComplement d) := by
  haveI : IsClosed (lpComplement d : Set (FourierL2 d)) := lpComplement_isClosed d
  infer_instance

theorem complementLinearized_norm_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : Frequency d → ℂ}
    (ha : ComplementSupported a) (k : Frequency d) :
    ‖complementLinearized μ a k‖ ≤ ‖a k‖ := by
  by_cases hk : ComplementFrequency k
  · have hgap := complement_linearized_gap hd hμ0 hμ2 hk
    have heig := complement_eigenvalue_ge_sixtyfour hd hk
    have heig0 : 0 < frequencyLength k ^ d := by linarith
    have hdiv : 0 ≤ μ / frequencyLength k ^ d := div_nonneg hμ0 heig0.le
    have hnon : 0 ≤ 1 - μ / frequencyLength k ^ d := by linarith
    simp only [complementLinearized, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnon]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  · simp [complementLinearized, ha k hk]

def lpComplementForward {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : lpComplement d) : lpComplement d := by
  let b : FourierL2 d := ⟨complementLinearized μ (a.val : Frequency d → ℂ),
    (lp.memℓp a.val).mono' (complementLinearized_norm_bound hd hμ0 hμ2 a.property)⟩
  exact ⟨b, complementLinearized_supported μ a.property⟩

def lpComplementInverse {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : lpComplement d) : lpComplement d := by
  let b : FourierL2 d := ⟨complementInverse μ (a.val : Frequency d → ℂ),
    ((lp.memℓp a.val).norm.const_mul (32/31:ℝ)).mono
      (complementInverse_norm_bound hd hμ0 hμ2 (a.val : Frequency d → ℂ))⟩
  exact ⟨b, complementInverse_supported μ (a.val : Frequency d → ℂ)⟩

@[simp] theorem lpComplementForward_apply {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : lpComplement d) (k : Frequency d) :
    (lpComplementForward hd hμ0 hμ2 a).val k =
      ((1 - μ / frequencyLength k ^ d : ℝ):ℂ) * a.val k := rfl

@[simp] theorem lpComplementInverse_apply {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : lpComplement d) (k : Frequency d) :
    (lpComplementInverse hd hμ0 hμ2 a).val k =
      (complementInverseMultiplier μ k : ℂ) * a.val k := rfl

theorem lpComplementForward_norm_le {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : lpComplement d) :
    ‖lpComplementForward hd hμ0 hμ2 a‖ ≤ ‖a‖ := by
  change ‖(lpComplementForward hd hμ0 hμ2 a).val‖ ≤ ‖a.val‖
  exact lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (complementLinearized_norm_bound hd hμ0 hμ2 a.property)

theorem lpComplementInverse_norm_le {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : lpComplement d) :
    ‖lpComplementInverse hd hμ0 hμ2 a‖ ≤ (32/31:ℝ)*‖a‖ := by
  have h : ‖(lpComplementInverse hd hμ0 hμ2 a).val‖ ≤ ‖((32/31:ℂ) • a.val)‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro k
    have h := complementInverse_norm_bound hd hμ0 hμ2 (a.val : Frequency d → ℂ) k
    change ‖complementInverse μ (a.val : Frequency d → ℂ) k‖ ≤ ‖(32/31:ℂ)*a.val k‖
    norm_num only [norm_mul, norm_div, Complex.norm_ofNat]
    exact h
  norm_num only [norm_smul, norm_div, Complex.norm_ofNat] at h
  exact h

/-- Genuine linear equivalence of the closed Fourier ℓ² complement. -/
def lpComplementLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : lpComplement d ≃ₗ[ℂ] lpComplement d where
  toFun := lpComplementForward hd hμ0 hμ2
  invFun := lpComplementInverse hd hμ0 hμ2
  left_inv a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    exact congrFun (complementInverse_left hd hμ0 hμ2 a.property) k
  right_inv a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    exact congrFun (complementInverse_right hd hμ0 hμ2 a.property) k
  map_add' a b := by
    apply Subtype.ext
    apply lp.ext
    funext k
    simp [lpComplementForward_apply, mul_add]
  map_smul' c a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    simp [lpComplementForward_apply, mul_left_comm]

/-- Bounded continuous inverse on an actual complete Hilbert space, with
forward norm ≤1 and inverse norm ≤32/31 uniformly in 0≤μ≤2 and d≥12. -/
def lpComplementContinuousLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : lpComplement d ≃L[ℂ] lpComplement d :=
  (lpComplementLinearEquiv hd hμ0 hμ2).toContinuousLinearEquivOfBounds 1 (32/31)
    (fun a => by
      change ‖lpComplementForward hd hμ0 hμ2 a‖ ≤ 1*‖a‖
      simpa only [one_mul] using lpComplementForward_norm_le hd hμ0 hμ2 a)
    (fun a => lpComplementInverse_norm_le hd hμ0 hμ2 a)

#print axioms lpComplement_isClosed
#print axioms lpComplementContinuousLinearEquiv

end BecknerOnofri.HighDim

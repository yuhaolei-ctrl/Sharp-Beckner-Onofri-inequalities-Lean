module

public import BecknerOnofri.ComplementSobolev

@[expose] public section

/-! The real complete Sobolev Fourier complement and its actual bounded inverse.
Conjugate symmetry is a proved invariant, and decoding yields real H^s functions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal ComplexConjugate
open MeasureTheory

namespace BecknerOnofri.HighDim

def ConjugateSymmetric {d : ℕ} (a : Frequency d → ℂ) : Prop :=
  ∀ k, a (-k) = conj (a k)

theorem frequencyLength_neg {d : ℕ} (k : Frequency d) : frequencyLength (-k) = frequencyLength k := by
  simp only [frequencyLength, Pi.neg_apply, Int.cast_neg, neg_sq]

theorem sobolevScale_neg {d : ℕ} (s : ℝ) (k : Frequency d) : sobolevScale s (-k) = sobolevScale s k := by
  simp only [sobolevScale, frequencyLength_neg]

theorem complementFrequency_iff_square {d : ℕ} (k : Frequency d) :
    ComplementFrequency k ↔ 2 ≤ latticeSquare k := by
  refine ⟨complement_latticeSquare_ge_two, ?_⟩
  intro hk
  constructor
  · intro hz
    have hzero := (latticeSquare_eq_zero_iff k).mpr hz
    omega
  · intro hfirst
    have hone := (latticeSquare_eq_one_iff k).mpr hfirst
    omega

theorem complementFrequency_neg {d : ℕ} (k : Frequency d) :
    ComplementFrequency (-k) ↔ ComplementFrequency k := by
  rw [complementFrequency_iff_square, complementFrequency_iff_square, latticeSquare_neg]

theorem complementInverseMultiplier_neg {d : ℕ} (μ : ℝ) (k : Frequency d) :
    complementInverseMultiplier μ (-k) = complementInverseMultiplier μ k := by
  by_cases hk : ComplementFrequency k
  · have hn := (complementFrequency_neg k).mpr hk
    simp [complementInverseMultiplier, hk, hn, frequencyLength_neg]
  · have hn : ¬ ComplementFrequency (-k) := (complementFrequency_neg k).not.mpr hk
    simp [complementInverseMultiplier, hk, hn]

theorem complementLinearized_conjugate {d : ℕ} (μ : ℝ) {a : Frequency d → ℂ}
    (ha : ConjugateSymmetric a) : ConjugateSymmetric (complementLinearized μ a) := by
  intro k
  simp only [complementLinearized, frequencyLength_neg, ha k, map_mul, Complex.conj_ofReal]

theorem complementInverse_conjugate {d : ℕ} (μ : ℝ) {a : Frequency d → ℂ}
    (ha : ConjugateSymmetric a) : ConjugateSymmetric (complementInverse μ a) := by
  intro k
  simp only [complementInverse, complementInverseMultiplier_neg, ha k, map_mul, Complex.conj_ofReal]

/-- Real Fourier Hilbert complement, with conjugate symmetry as a closed linear constraint. -/
def realLpComplement (d : ℕ) : Submodule ℝ (lpComplement d) where
  carrier := {a | ConjugateSymmetric (a.val : Frequency d → ℂ)}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro a b ha hb k
    change a.val (-k) + b.val (-k) = conj (a.val k + b.val k)
    rw [ha k, hb k, map_add]
  smul_mem' := by
    intro c a ha k
    change (c:ℂ)*a.val (-k) = conj ((c:ℂ)*a.val k)
    rw [ha k, map_mul, Complex.conj_ofReal]

theorem realLpComplement_isClosed (d : ℕ) :
    IsClosed (realLpComplement d : Set (lpComplement d)) := by
  change IsClosed {a : lpComplement d | ∀ k, a.val (-k) = conj (a.val k)}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_eq
    ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 (-k)).continuous.comp continuous_subtype_val)
    (Complex.continuous_conj.comp
      ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 k).continuous.comp continuous_subtype_val))

instance realLpComplement_completeSpace (d : ℕ) : CompleteSpace (realLpComplement d) := by
  haveI : IsClosed (realLpComplement d : Set (lpComplement d)) := realLpComplement_isClosed d
  infer_instance

def realComplementForward {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : realLpComplement d) : realLpComplement d :=
  ⟨lpComplementForward hd hμ0 hμ2 a.val, complementLinearized_conjugate μ a.property⟩

def realComplementInverse {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : realLpComplement d) : realLpComplement d :=
  ⟨lpComplementInverse hd hμ0 hμ2 a.val, complementInverse_conjugate μ a.property⟩

def realComplementLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : realLpComplement d ≃ₗ[ℝ] realLpComplement d where
  toFun := realComplementForward hd hμ0 hμ2
  invFun := realComplementInverse hd hμ0 hμ2
  left_inv a := by apply Subtype.ext; exact (lpComplementLinearEquiv hd hμ0 hμ2).left_inv a.val
  right_inv a := by apply Subtype.ext; exact (lpComplementLinearEquiv hd hμ0 hμ2).right_inv a.val
  map_add' a b := by
    apply Subtype.ext
    exact (lpComplementLinearEquiv hd hμ0 hμ2).map_add a.val b.val
  map_smul' c a := by
    apply Subtype.ext
    exact (lpComplementLinearEquiv hd hμ0 hμ2).map_smul_of_tower c a.val

/-- The real Banach-space inverse needed by the Lyapunov--Schmidt/IFT step. -/
def realComplementContinuousLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : realLpComplement d ≃L[ℝ] realLpComplement d where
  toLinearEquiv := realComplementLinearEquiv hd hμ0 hμ2
  continuous_toFun :=
    ((lpComplementContinuousLinearEquiv hd hμ0 hμ2).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((lpComplementContinuousLinearEquiv hd hμ0 hμ2).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

theorem fourierCoeff_conjugate {d : ℕ} (u : Torus d → ℝ) : ConjugateSymmetric (fourierCoeff u) := by
  intro k
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [neg_neg, map_mul, Complex.conj_ofReal, ← UnitAddTorus.mFourier_neg])

theorem scaledFourier_conjugate {d : ℕ} (s : ℝ) (u : Torus d → ℝ) :
    ConjugateSymmetric (scaledFourier s u) := by
  intro k
  simp only [scaledFourier, sobolevScale_neg, fourierCoeff_conjugate u k,
    map_mul, Complex.conj_ofReal]

theorem unscale_conjugate {d : ℕ} (s : ℝ) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) : ConjugateSymmetric (unscaleSobolev s a) := by
  intro k
  simp only [unscaleSobolev, sobolevScale_neg, ha k, map_mul, Complex.conj_ofReal]

theorem fourierCoeff_star_L2 {d : ℕ} (f : Lp ℂ 2 (torusMeasure d)) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (star f : Lp ℂ 2 (torusMeasure d)) k =
      conj (UnitAddTorus.mFourierCoeff f (-k)) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  simp only [hx, Pi.star_apply, neg_neg, smul_eq_mul, map_mul, ← UnitAddTorus.mFourier_neg]
  rfl

theorem decodeSobolev_star {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) :
    star (decodeSobolev hs a) = decodeSobolev hs a := by
  apply (UnitAddTorus.mFourierBasis (d := Fin d)).repr.injective
  apply lp.ext
  funext k
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr]
  calc
    _ = conj (UnitAddTorus.mFourierCoeff (decodeSobolev hs a) (-k)) :=
      fourierCoeff_star_L2 (decodeSobolev hs a) k
    _ = conj (unscaleSobolev s a (-k)) := congrArg _ (decodeSobolev_fourier hs a (-k))
    _ = unscaleSobolev s a k := by rw [unscale_conjugate s a ha k, starRingEnd_self_apply]
    _ = _ := (decodeSobolev_fourier hs a k).symm

theorem decodeSobolev_im_zero {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) :
    ∀ᵐ x ∂torusMeasure d, (decodeSobolev hs a x).im = 0 := by
  have h := Lp.coeFn_star (decodeSobolev hs a)
  rw [decodeSobolev_star hs a ha] at h
  filter_upwards [h] with x hx
  have hi : (decodeSobolev hs a x).im = -(decodeSobolev hs a x).im := by
    simpa only [Pi.star_apply, Complex.star_def, Complex.conj_im] using congrArg Complex.im hx
  linarith

/-- Actual real function represented by a conjugate-symmetric weighted sequence. -/
def decodeRealSobolev {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d) : Torus d → ℝ :=
  fun x => (decodeSobolev hs a x).re

theorem decodeRealSobolev_fourier {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) (k : Frequency d) :
    fourierCoeff (decodeRealSobolev hs a) k = unscaleSobolev s a k := by
  rw [← decodeSobolev_fourier hs a k]
  unfold fourierCoeff UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [decodeSobolev_im_zero hs a ha] with x hx
  change _ * ((decodeSobolev hs a x).re : ℂ) = _ * decodeSobolev hs a x
  congr 1
  apply Complex.ext
  · rfl
  · simpa using hx.symm

theorem decodeRealSobolev_mem {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) :
    InSobolev s (decodeRealSobolev hs a) := by
  refine ⟨(Lp.memLp (decodeSobolev hs a)).re, ?_⟩
  exact (unscale_sobolev_summable s a).congr (fun k => by
    unfold sobolevTerm
    rw [decodeRealSobolev_fourier hs a ha])

#print axioms realComplementContinuousLinearEquiv
#print axioms decodeRealSobolev_mem

end BecknerOnofri.HighDim

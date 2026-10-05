import BecknerOnofri.ComplementOperator

/-! Exact weighted Fourier encoding of the source Sobolev spaces. The bounded
complement inverse acts on this complete ℓ² representation for every s. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory

namespace BecknerOnofri.HighDim

/-- Square root of the exact source H^s Fourier weight. -/
def sobolevScale {d : ℕ} (s : ℝ) (k : Frequency d) : ℝ :=
  (1 + (2 * Real.pi * frequencyLength k)^2)^(s/2)

theorem sobolevScale_pos {d : ℕ} (s : ℝ) (k : Frequency d) : 0 < sobolevScale s k :=
  Real.rpow_pos_of_pos (by nlinarith [sq_nonneg (2*Real.pi*frequencyLength k)]) _

theorem sobolevScale_sq {d : ℕ} (s : ℝ) (k : Frequency d) :
    sobolevScale s k ^ 2 = (1+(2*Real.pi*frequencyLength k)^2)^s := by
  unfold sobolevScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

def scaledFourier {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (k : Frequency d) : ℂ :=
  (sobolevScale s k : ℂ) * fourierCoeff u k

theorem scaledFourier_norm_sq {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (k : Frequency d) :
    ‖scaledFourier s u k‖^2 = sobolevTerm s u k := by
  simp only [scaledFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sobolevScale_pos s k), mul_pow, sobolevScale_sq, sobolevTerm]

/-- Every actual H^s function has a square-summable encoded Fourier sequence. -/
def encodeSobolev {d : ℕ} {s : ℝ} (u : Torus d → ℝ) (hu : InSobolev s u) : FourierL2 d :=
  ⟨scaledFourier s u, (memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)).mpr (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, scaledFourier_norm_sq] using hu.2)⟩

@[simp] theorem encodeSobolev_apply {d : ℕ} {s : ℝ} (u : Torus d → ℝ)
    (hu : InSobolev s u) (k : Frequency d) : encodeSobolev u hu k = scaledFourier s u k := rfl

/-- This is exactly the norm in the trusted raw-function statement. -/
theorem encodeSobolev_norm {d : ℕ} {s : ℝ} (u : Torus d → ℝ) (hu : InSobolev s u) :
    ‖encodeSobolev u hu‖ = sobolevNorm s u := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) (encodeSobolev u hu)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, encodeSobolev_apply, scaledFourier_norm_sq] at h
  unfold sobolevNorm
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- Decode weighted ℓ² coordinates to the actual Fourier coefficients. -/
def unscaleSobolev {d : ℕ} (s : ℝ) (a : FourierL2 d) (k : Frequency d) : ℂ :=
  ((sobolevScale s k)⁻¹ : ℝ) * a k

theorem unscale_encodeSobolev {d : ℕ} {s : ℝ} (u : Torus d → ℝ)
    (hu : InSobolev s u) : unscaleSobolev s (encodeSobolev u hu) = fourierCoeff u := by
  funext k
  have hn : (sobolevScale s k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sobolevScale_pos s k).ne'
  simp only [unscaleSobolev, encodeSobolev_apply, scaledFourier, Complex.ofReal_inv,
    ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem unscale_weighted_norm_sq {d : ℕ} (s : ℝ) (a : FourierL2 d) (k : Frequency d) :
    (1+(2*Real.pi*frequencyLength k)^2)^s * ‖unscaleSobolev s a k‖^2 = ‖a k‖^2 := by
  rw [← sobolevScale_sq]
  simp only [unscaleSobolev, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sobolevScale_pos s k)), mul_pow, inv_pow]
  field_simp [(sobolevScale_pos s k).ne']

/-- Every encoded vector represents a genuinely summable H^s Fourier sequence. -/
theorem unscale_sobolev_summable {d : ℕ} (s : ℝ) (a : FourierL2 d) :
    Summable (fun k => (1+(2*Real.pi*frequencyLength k)^2)^s * ‖unscaleSobolev s a k‖^2) := by
  simp only [unscale_weighted_norm_sq]
  have h := (lp.memℓp a).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem encodeSobolev_complement {d : ℕ} {s : ℝ} (u : Torus d → ℝ)
    (hu : InSobolev s u) (hcomp : ComplementSupported (fourierCoeff u)) :
    encodeSobolev u hu ∈ lpComplement d := by
  intro k hk
  simp [encodeSobolev_apply, scaledFourier, hcomp k hk]

/-- Exact coefficient action after weighting: the Hilbert-space inverse is
still the same Fourier multiplier in every H^s norm. -/
theorem unscale_complementInverse {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (s : ℝ) (a : lpComplement d) (k : Frequency d) :
    unscaleSobolev s (lpComplementInverse hd hμ0 hμ2 a).val k =
      (complementInverseMultiplier μ k : ℂ) * unscaleSobolev s a.val k := by
  simp only [unscaleSobolev, lpComplementInverse_apply]
  ring

/-- The forward multiplier also commutes with the exact Sobolev weighting. -/
theorem unscale_complementForward {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (s : ℝ) (a : lpComplement d) (k : Frequency d) :
    unscaleSobolev s (lpComplementForward hd hμ0 hμ2 a).val k =
      ((1-μ/frequencyLength k^d:ℝ):ℂ) * unscaleSobolev s a.val k := by
  simp only [unscaleSobolev, lpComplementForward_apply]
  ring


theorem sobolevScale_ge_one {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (k : Frequency d) :
    1 ≤ sobolevScale s k := by
  exact Real.one_le_rpow (by nlinarith [sq_nonneg (2*Real.pi*frequencyLength k)]) (by linarith)

theorem unscale_norm_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d) (k : Frequency d) :
    ‖unscaleSobolev s a k‖ ≤ ‖a k‖ := by
  have hpos := sobolevScale_pos s k
  simp only [unscaleSobolev, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (sobolevScale_ge_one hs k))

/-- The decoded coefficients genuinely lie in ordinary Fourier ℓ² when s≥0. -/
def unscaledLp {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d) : FourierL2 d :=
  ⟨unscaleSobolev s a, (lp.memℓp a).mono' (unscale_norm_le hs a)⟩

/-- Reconstruction using the actual complete Fourier basis on Haar L²(T^d). -/
def decodeSobolev {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : FourierL2 d) :
    Lp ℂ 2 (torusMeasure d) :=
  (UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm (unscaledLp hs a)

theorem decodeSobolev_fourier {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (a : FourierL2 d) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (decodeSobolev hs a) k = unscaleSobolev s a k := by
  calc
    _ = (UnitAddTorus.mFourierBasis (d := Fin d)).repr (decodeSobolev hs a) k :=
      (UnitAddTorus.mFourierBasis_repr (decodeSobolev hs a) k).symm
    _ = _ := by simp only [decodeSobolev, LinearIsometryEquiv.apply_symm_apply]; rfl

/-- The inverse coefficient sequence corresponds to an actual Haar-L² function
and has the exact required weighted Sobolev summability. -/
theorem decoded_inverse_sobolev {d : ℕ} (hd : 12 ≤ d) {μ s : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (hs : 0 ≤ s) (a : lpComplement d) :
    Summable (fun k => (1+(2*Real.pi*frequencyLength k)^2)^s *
      ‖UnitAddTorus.mFourierCoeff (decodeSobolev hs (lpComplementInverse hd hμ0 hμ2 a).val) k‖^2) := by
  simp only [decodeSobolev_fourier]
  exact unscale_sobolev_summable s _

#print axioms encodeSobolev_norm
#print axioms unscale_sobolev_summable
#print axioms unscale_complementInverse

end BecknerOnofri.HighDim

module

public import BecknerOnofri.GreenContinuous
public import BecknerOnofri.RealComplementOperator

@[expose] public section

/-! The genuine Green map Fourier ℓ²→C(T^d), bounded by Cauchy–Schwarz.
This regularizing map upgrades the Hilbert inverse to the continuous-function setting. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

namespace BecknerOnofri.HighDim

/-- Fourier ℓ² vector of the actual normalized real Green kernel. -/
def greenFourierVector (d : ℕ) : FourierL2 d :=
  (UnitAddTorus.mFourierBasis (d := Fin d)).repr
    ((Legacy.BecknerOnofri.GreenRoughEnergy.kernel_memLp d).ofReal.toLp
      (fun x => (normalizedGreenKernel d x : ℂ)))

theorem greenFourierVector_apply {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    greenFourierVector d k = ((if k=0 then 0 else 1/frequencyLength k^d : ℝ):ℂ) := by
  calc
    _ = UnitAddTorus.mFourierCoeff
        ((Legacy.BecknerOnofri.GreenRoughEnergy.kernel_memLp d).ofReal.toLp
          (fun x => (normalizedGreenKernel d x : ℂ))) k :=
      UnitAddTorus.mFourierBasis_repr _ k
    _ = fourierCoeff (normalizedGreenKernel d) k :=
      Legacy.TorusEndpoint.GreenPairing.fourierCoeff_real_toLp
        (Legacy.BecknerOnofri.GreenRoughEnergy.kernel_memLp d) k
    _ = _ := normalizedGreenKernel_fourier hd k

theorem green_series_summable (d : ℕ) (a : FourierL2 d) :
    Summable (fun k => ‖greenFourierVector d k * a k‖) := by
  simp only [norm_mul]
  exact lp.summable_mul (by simpa using Real.HolderConjugate.two_two) (greenFourierVector d) a

def greenLiftComplexValue (d : ℕ) (a : FourierL2 d) : Torus d → ℂ :=
  Legacy.TorusEndpoint.absoluteFourierSeries (fun k => greenFourierVector d k * a k)

theorem greenLiftComplexValue_continuous (d : ℕ) (a : FourierL2 d) :
    Continuous (greenLiftComplexValue d a) :=
  Legacy.TorusEndpoint.absoluteFourierSeries_continuous _ (green_series_summable d a)

theorem greenLiftComplexValue_bound (d : ℕ) (a : FourierL2 d) (x : Torus d) :
    ‖greenLiftComplexValue d a x‖ ≤ ‖greenFourierVector d‖ * ‖a‖ := by
  calc
    _ ≤ ∑' k, ‖greenFourierVector d k * a k * UnitAddTorus.mFourier k x‖ :=
      norm_tsum_le_tsum_norm (Legacy.TorusEndpoint.summable_fourierSeries_apply _
        (green_series_summable d a) x).norm
    _ = ∑' k, ‖greenFourierVector d k‖ * ‖a k‖ := by
      simp only [norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply, mul_one]
    _ ≤ _ := lp.tsum_mul_le_mul_norm' (by simpa using Real.HolderConjugate.two_two)
      (greenFourierVector d) a

def greenLiftComplexLinear (d : ℕ) : FourierL2 d →ₗ[ℂ] C(Torus d, ℂ) where
  toFun a := ⟨greenLiftComplexValue d a, greenLiftComplexValue_continuous d a⟩
  map_add' a b := by
    ext x
    change (∑' k, greenFourierVector d k * (a k+b k) * UnitAddTorus.mFourier k x) = _
    simp only [mul_add, add_mul]
    exact (Legacy.TorusEndpoint.summable_fourierSeries_apply _ (green_series_summable d a) x).tsum_add
      (Legacy.TorusEndpoint.summable_fourierSeries_apply _ (green_series_summable d b) x)
  map_smul' c a := by
    ext x
    change (∑' k, greenFourierVector d k * (c*a k) * UnitAddTorus.mFourier k x) =
      c * ∑' k, greenFourierVector d k * a k * UnitAddTorus.mFourier k x
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    ring

/-- Bounded actual Green regularization from Fourier ℓ² into continuous functions. -/
def greenLiftComplex (d : ℕ) : FourierL2 d →L[ℂ] C(Torus d, ℂ) :=
  (greenLiftComplexLinear d).mkContinuous ‖greenFourierVector d‖ (fun a => by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    exact greenLiftComplexValue_bound d a)

theorem greenLiftComplex_norm_le (d : ℕ) (a : FourierL2 d) :
    ‖greenLiftComplex d a‖ ≤ ‖greenFourierVector d‖ * ‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  exact greenLiftComplexValue_bound d a

theorem greenLiftComplex_fourier {d : ℕ} (hd : 0 < d) (a : FourierL2 d) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (greenLiftComplex d a) k =
      ((if k=0 then 0 else 1/frequencyLength k^d : ℝ):ℂ) * a k := by
  calc
    _ = greenFourierVector d k * a k :=
      Legacy.TorusEndpoint.absoluteFourierSeries_coefficient _ (green_series_summable d a) k
    _ = _ := by rw [greenFourierVector_apply hd]

theorem greenFourierVector_conjugate {d : ℕ} (hd : 0 < d) :
    ConjugateSymmetric (greenFourierVector d : Frequency d → ℂ) := by
  intro k
  rw [greenFourierVector_apply hd, greenFourierVector_apply hd]
  simp only [frequencyLength_neg, neg_eq_zero, Complex.conj_ofReal]

theorem greenLiftComplex_real {d : ℕ} (hd : 0 < d) (a : FourierL2 d)
    (ha : ConjugateSymmetric (a : Frequency d → ℂ)) (x : Torus d) :
    (greenLiftComplex d a x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change conj (∑' k, (greenFourierVector d k * a k) * UnitAddTorus.mFourier k x) = _
  rw [Complex.conj_tsum]
  calc
    _ = ∑' k, (greenFourierVector d (-k) * a (-k)) * UnitAddTorus.mFourier (-k) x := by
      apply tsum_congr
      intro k
      rw [map_mul, map_mul, greenFourierVector_conjugate hd k, ha k, UnitAddTorus.mFourier_neg]
    _ = _ := (Equiv.neg (Frequency d)).tsum_eq
      (fun k => (greenFourierVector d k*a k)*UnitAddTorus.mFourier k x)

/-- Real-valued regularization of real Fourier-complement vectors. -/
def greenLiftRealLinear {d : ℕ} (hd : 0 < d) : realLpComplement d →ₗ[ℝ] C(Torus d, ℝ) where
  toFun a := ⟨fun x => (greenLiftComplex d a.val.val x).re,
    Complex.continuous_re.comp (greenLiftComplex d a.val.val).continuous⟩
  map_add' a b := by
    ext x
    change (greenLiftComplex d (a.val.val + b.val.val) x).re = _
    rw [map_add]
    rfl
  map_smul' c a := by
    ext x
    change (greenLiftComplex d (c • a.val.val) x).re = c * (greenLiftComplex d a.val.val x).re
    rw [(greenLiftComplex d).map_smul_of_tower c]
    simp [ContinuousMap.smul_apply, Complex.real_smul]

def greenLiftReal {d : ℕ} (hd : 0 < d) : realLpComplement d →L[ℝ] C(Torus d, ℝ) :=
  (greenLiftRealLinear hd).mkContinuous ‖greenFourierVector d‖ (fun a => by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro x
    exact (Complex.abs_re_le_norm _).trans (greenLiftComplexValue_bound d a.val.val x))

theorem greenLiftReal_fourier {d : ℕ} (hd : 0 < d) (a : realLpComplement d) (k : Frequency d) :
    fourierCoeff (greenLiftReal hd a) k =
      ((if k=0 then 0 else 1/frequencyLength k^d : ℝ):ℂ) * a.val.val k := by
  have he (x : Torus d) : ((greenLiftReal hd a x : ℝ):ℂ) = greenLiftComplex d a.val.val x := by
    apply Complex.ext
    · rfl
    · exact (greenLiftComplex_real hd a.val.val a.property x).symm
  calc
    _ = UnitAddTorus.mFourierCoeff (greenLiftComplex d a.val.val) k := by
      unfold fourierCoeff UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [he]; rfl)
    _ = _ := greenLiftComplex_fourier hd a.val.val k

#print axioms greenLiftComplex
#print axioms greenLiftReal_fourier

end BecknerOnofri.HighDim

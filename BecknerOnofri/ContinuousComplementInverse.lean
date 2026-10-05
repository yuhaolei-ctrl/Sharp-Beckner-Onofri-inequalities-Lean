module

public import BecknerOnofri.GreenHilbertContinuous
public import BecknerOnofri.ContinuousFirstShell

@[expose] public section

/-! The actual Green linearization on the closed continuous first-shell complement
is a bounded real Banach-space isomorphism. The inverse is obtained from the
Fourier Hilbert inverse by the genuine L²-to-C Green regularization. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim
open ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.TorusSobolev

/-- Actual Fourier transform of a real continuous torus function. -/
def continuousFourier (d : ℕ) : Space d →L[ℝ] FourierL2 d :=
  ((fourierIsometry d).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp (toL2 d)

@[simp] theorem continuousFourier_apply {d : ℕ} (f : Space d) (k : Frequency d) :
    continuousFourier d f k = coefficient k f := rfl

def continuousComplementLp (d : ℕ) : complement d →L[ℝ] lpComplement d :=
  ((continuousFourier d).comp (complement d).subtypeL).codRestrict
    ((lpComplement d).restrictScalars ℝ) (fun f => by
      intro k hk
      exact (mem_complement_fourier_iff f.val).mp f.property k hk)

def continuousComplementFourier (d : ℕ) : complement d →L[ℝ] realLpComplement d :=
  (continuousComplementLp d).codRestrict (realLpComplement d) (fun f => by
    intro k
    exact coefficient_neg k f.val)

@[simp] theorem continuousComplementFourier_apply {d : ℕ} (f : complement d) (k : Frequency d) :
    (continuousComplementFourier d f).val.val k = coefficient k f.val := rfl

theorem continuousComplementFourier_injective (d : ℕ) :
    Function.Injective (continuousComplementFourier d) := by
  intro f g h
  apply Subtype.ext
  apply coefficient_ext
  intro k
  exact congrArg (fun a : realLpComplement d => a.val.val k) h

theorem coefficient_green {d : ℕ} (hd : 0 < d) (f : Space d) (k : Frequency d) :
    coefficient k (greenContinuous d f) =
      ((if k=0 then 0 else 1/frequencyLength k^d : ℝ):ℂ) * coefficient k f := by
  simp only [coefficient_eq_fourierCoeff]
  exact greenContinuous_fourier hd f k

theorem greenContinuous_mem_complement {d : ℕ} (hd : 0 < d) (f : complement d) :
    greenContinuous d f.val ∈ complement d := by
  rw [mem_complement_fourier_iff]
  intro k hk
  rw [coefficient_green hd, (mem_complement_fourier_iff f.val).mp f.property k hk, mul_zero]

/-- Actual normalized Green convolution restricted to the closed complement. -/
def continuousComplementGreen {d : ℕ} (hd : 0 < d) : complement d →L[ℝ] complement d :=
  ((greenContinuous d).comp (complement d).subtypeL).codRestrict
    (complement d) (greenContinuous_mem_complement hd)

@[simp] theorem continuousComplementGreen_coe {d : ℕ} (hd : 0 < d) (f : complement d) :
    (continuousComplementGreen hd f).val = greenContinuous d f.val := rfl

def continuousComplementForward {d : ℕ} (hd : 0 < d) (μ : ℝ) :
    complement d →L[ℝ] complement d :=
  (((ContinuousLinearMap.id ℝ (Space d)) - μ • greenContinuous d).comp
    (complement d).subtypeL).codRestrict (complement d) (fun f => by
      exact (complement d).sub_mem f.property
        ((complement d).smul_mem μ (greenContinuous_mem_complement hd f)))

@[simp] theorem continuousComplementForward_coe {d : ℕ} (hd : 0 < d) (μ : ℝ) (f : complement d) :
    (continuousComplementForward hd μ f).val = f.val - μ • greenContinuous d f.val := rfl

theorem continuousComplementForward_eq {d : ℕ} (hd : 0 < d) (μ : ℝ) :
    continuousComplementForward hd μ = ContinuousLinearMap.id ℝ (complement d) -
      μ • continuousComplementGreen hd := by
  ext f : 1
  rfl

theorem continuousComplementForward_fourier {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (f : complement d) :
    continuousComplementFourier d (continuousComplementForward (by omega) μ f) =
      realComplementForward hd hμ0 hμ2 (continuousComplementFourier d f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply lp.ext
  funext k
  simp only [continuousComplementFourier_apply, continuousComplementForward_coe,
    map_sub, map_smul]
  change coefficient k f.val - μ • coefficient k (greenContinuous d f.val) =
    ((1-μ/frequencyLength k^d:ℝ):ℂ) * coefficient k f.val
  rw [coefficient_green (by omega)]
  by_cases hk : k=0
  · have hz := (mem_complement_fourier_iff f.val).mp f.property k (by simp [ComplementFrequency, hk])
    simp [hz]
  · simp only [if_neg hk, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div]
    ring

def continuousComplementInverseValue {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : complement d →L[ℝ] Space d :=
  (complement d).subtypeL + μ • ((greenLiftReal (by omega)).comp
    ((realComplementContinuousLinearEquiv hd hμ0 hμ2).symm.toContinuousLinearMap.comp
      (continuousComplementFourier d)))

@[simp] theorem continuousComplementInverseValue_apply {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (f : complement d) :
    continuousComplementInverseValue hd hμ0 hμ2 f = f.val +
      μ • greenLiftReal (by omega) (realComplementInverse hd hμ0 hμ2 (continuousComplementFourier d f)) := rfl

theorem continuousComplementInverseValue_fourier {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (f : complement d) (k : Frequency d) :
    coefficient k (continuousComplementInverseValue hd hμ0 hμ2 f) =
      (realComplementInverse hd hμ0 hμ2 (continuousComplementFourier d f)).val.val k := by
  rw [continuousComplementInverseValue_apply, map_add, map_smul]
  rw [coefficient_eq_fourierCoeff k (greenLiftReal _ _), greenLiftReal_fourier]
  let a := continuousComplementFourier d f
  have h := congrFun (complementInverse_right hd hμ0 hμ2 a.val.property) k
  change ((1-μ/frequencyLength k^d:ℝ):ℂ)*
      (realComplementInverse hd hμ0 hμ2 a).val.val k = coefficient k f.val at h
  by_cases hk : k=0
  · have hz := (mem_complement_fourier_iff f.val).mp f.property k (by simp [ComplementFrequency, hk])
    have hb := (realComplementInverse hd hμ0 hμ2 a).val.property k (by simp [ComplementFrequency, hk])
    simpa only [if_pos hk, Complex.ofReal_zero, zero_mul, smul_zero, add_zero, hz] using hb.symm
  · simp only [if_neg hk, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    push_cast at h ⊢
    linear_combination -h

def continuousComplementInverse {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : complement d →L[ℝ] complement d :=
  (continuousComplementInverseValue hd hμ0 hμ2).codRestrict (complement d) (fun f => by
    rw [mem_complement_fourier_iff]
    intro k hk
    rw [continuousComplementInverseValue_fourier]
    exact (realComplementInverse hd hμ0 hμ2 (continuousComplementFourier d f)).val.property k hk)

theorem continuousComplementInverse_fourier {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (f : complement d) :
    continuousComplementFourier d (continuousComplementInverse hd hμ0 hμ2 f) =
      realComplementInverse hd hμ0 hμ2 (continuousComplementFourier d f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply lp.ext
  funext k
  exact continuousComplementInverseValue_fourier hd hμ0 hμ2 f k

/-- Genuine real continuous-function inverse on the closed full first-shell complement. -/
def continuousComplementLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : complement d ≃ₗ[ℝ] complement d where
  toFun := continuousComplementForward (by omega) μ
  invFun := continuousComplementInverse hd hμ0 hμ2
  left_inv f := by
    apply continuousComplementFourier_injective d
    rw [continuousComplementInverse_fourier, continuousComplementForward_fourier]
    exact (realComplementLinearEquiv hd hμ0 hμ2).left_inv _
  right_inv f := by
    apply continuousComplementFourier_injective d
    rw [continuousComplementForward_fourier, continuousComplementInverse_fourier]
    exact (realComplementLinearEquiv hd hμ0 hμ2).right_inv _
  map_add' := map_add _
  map_smul' := map_smul _

def continuousComplementContinuousLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : complement d ≃L[ℝ] complement d where
  toLinearEquiv := continuousComplementLinearEquiv hd hμ0 hμ2
  continuous_toFun := (continuousComplementForward (by omega) μ).continuous
  continuous_invFun := (continuousComplementInverse hd hμ0 hμ2).continuous

/-- Exact operator underlying the Banach isomorphism: I minus μ times actual Green convolution. -/
theorem continuousComplementContinuousLinearEquiv_toCLM {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) :
    (continuousComplementContinuousLinearEquiv hd hμ0 hμ2).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (complement d) - μ • continuousComplementGreen (by omega) := by
  exact continuousComplementForward_eq (by omega) μ

theorem continuousComplementContinuousLinearEquiv_one {d : ℕ} (hd : 12 ≤ d) :
    (continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ)≤1)
      (by norm_num : (1:ℝ)≤2)).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (complement d) - continuousComplementGreen (by omega) := by
  simpa only [one_smul] using continuousComplementContinuousLinearEquiv_toCLM hd
    (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2)

#print axioms continuousComplementContinuousLinearEquiv
end BecknerOnofri.HighDim

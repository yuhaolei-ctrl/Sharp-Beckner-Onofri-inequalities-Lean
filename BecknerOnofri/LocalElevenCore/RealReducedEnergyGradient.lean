import BecknerOnofri.LocalElevenCore.ReducedEnergyGradient
import BecknerOnofri.LocalElevenCore.ActiveAmplitudeFactor

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.RealReducedEnergy
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation ReducedEnergyGradient

/-- The finite real coordinate pairing as a continuous linear map into the dual. -/
def dotDual (d : ℕ) : Amplitudes d →L[ℝ] (Amplitudes d →L[ℝ] ℝ) :=
  ∑ i : Fin d,(ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

@[simp] theorem dotDual_apply {d : ℕ} (r h : Amplitudes d) : dotDual d r h=∑ i,h i*r i := by
  simp [dotDual,ContinuousLinearMap.sum_apply,mul_comm]

def reCoordinates (d : ℕ) : Coordinates d →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem reCoordinates_apply {d : ℕ} (z : Coordinates d) (i : Fin d) :
    reCoordinates d z i=(z i).re := rfl

def residual {d : ℕ} (hd : 11≤d) (μ : ℝ) (r : Amplitudes d) : Amplitudes d :=
  reCoordinates d (reduced hd (μ,realCoordinates d r))

def energy {d : ℕ} (hd : 11≤d) (μ : ℝ) (r : Amplitudes d) : ℝ :=
  physicalReducedEnergy hd (μ,realCoordinates d r)

def gradient {d : ℕ} (hd : 11≤d) (μ : ℝ) (r : Amplitudes d) : Amplitudes d →L[ℝ] ℝ :=
  -(2/μ) • dotDual d (residual hd μ r)

@[simp] theorem gradient_apply {d : ℕ} (hd : 11≤d) (μ : ℝ) (r h : Amplitudes d) :
    gradient hd μ r h=-(2/μ)*(∑ i,h i*(reduced hd (μ,realCoordinates d r) i).re) := by
  simp [gradient,dotDual_apply,residual]

theorem hasFDerivAt_energy {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),HasFDerivAt (energy hd x.1) (gradient hd x.1 x.2) x.2 := by
  have ht := ActiveAmplitudeFactor.realEmbedding_tendsto d
  filter_upwards [ht.eventually (hasFDerivAt_physicalReducedEnergy hd),
    ht.eventually (fderiv_physicalReducedEnergy_apply hd)] with x hf he
  have h := hf.comp x.2 (realCoordinates d).hasFDerivAt
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro r
  rw [ContinuousLinearMap.comp_apply,← hf.fderiv,he]
  simp only [gradient_apply,Complex.re_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    realCoordinates_apply,Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,sub_zero,
    ActiveAmplitudeFactor.realEmbedding_apply]

theorem hasFDerivAt_gradient {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),HasFDerivAt (gradient hd x.1)
      (-(2/x.1) • (dotDual d).comp ((reCoordinates d).comp
        ((fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2)).comp (realCoordinates d)))) x.2 := by
  filter_upwards [(ActiveAmplitudeFactor.realEmbedding_tendsto d).eventually
    (reduced_analytic hd).eventually_analyticAt] with x hx
  change AnalyticAt ℝ (reduced hd) (x.1,realCoordinates d x.2) at hx
  have hinc : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      (ContinuousLinearMap.inr ℝ ℝ (Coordinates d)) (realCoordinates d x.2) := by
    convert! (hasFDerivAt_const x.1 (realCoordinates d x.2)).prodMk
      (hasFDerivAt_id (realCoordinates d x.2)) using 1
  have hR : DifferentiableAt ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) :=
    hx.differentiableAt.comp (realCoordinates d x.2) hinc.differentiableAt
  exact (((dotDual d).hasFDerivAt.comp x.2 ((reCoordinates d).hasFDerivAt.comp x.2
    (hR.hasFDerivAt.comp x.2 (realCoordinates d).hasFDerivAt))).const_smul (-(2/x.1)))

#print axioms hasFDerivAt_energy
#print axioms hasFDerivAt_gradient
end BecknerOnofri.HighDim.LocalEleven.RealReducedEnergy

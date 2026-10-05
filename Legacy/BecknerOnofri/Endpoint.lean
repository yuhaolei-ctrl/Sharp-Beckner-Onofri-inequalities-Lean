module

public import Legacy.D10.CircleEntropy
public import Legacy.TorusEndpoint.EndpointSharpness
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
Actual Fourier endpoint statements, with summability included. The general
and dimensions-one-through-ten statements below are definitions of targets.
Only dimension one is proved here. General sharpness gives the necessary
upper bound on a valid coefficient, not validity in the remaining dimensions.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.BecknerOnofri

noncomputable def endpointConstant (d : ℕ) : ℝ :=
  (d : ℝ) / Legacy.TorusEndpoint.endpointSigma d

noncomputable def fourierEnergy {d : ℕ}
    (rho : Legacy.TorusEndpoint.ProbabilityDensity d) : ℝ :=
  ∑' k : Legacy.TorusEndpoint.NonzeroFrequency d, Legacy.TorusEndpoint.densitySpectralTerm rho k

/-- The genuine finite-entropy endpoint, including convergence of its energy. -/
def Endpoint (d : ℕ) : Prop :=
  ∀ rho : Legacy.TorusEndpoint.ProbabilityDensity d, rho.FiniteEntropy →
    Summable (Legacy.TorusEndpoint.densitySpectralTerm rho) ∧
      endpointConstant d * fourierEnergy rho ≤ Legacy.TorusEndpoint.densityEntropy rho.value

/-- The requested low-dimensional Fourier target. This is not a proved theorem. -/
def EndpointThroughTen : Prop := ∀ d : ℕ, 1 ≤ d → d ≤ 10 → Endpoint d

/-- Every coefficient above the proposed endpoint fails on an actual density. -/
def Sharpness (d : ℕ) : Prop :=
  ∀ C : ℝ, endpointConstant d < C →
    ∃ rho : Legacy.TorusEndpoint.ProbabilityDensity d,
      rho.FiniteEntropy ∧ Summable (Legacy.TorusEndpoint.densitySpectralTerm rho) ∧
        Legacy.TorusEndpoint.densityEntropy rho.value < C * fourierEnergy rho

theorem endpointSigma_one : Legacy.TorusEndpoint.endpointSigma 1 = 2 := by
  unfold Legacy.TorusEndpoint.endpointSigma
  norm_num only [Nat.cast_one]
  rw [Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  exact mul_div_cancel_right₀ 2 (Real.sqrt_pos.mpr Real.pi_pos).ne'

theorem endpointConstant_one : endpointConstant 1 = 1 / 2 := by
  simp [endpointConstant, endpointSigma_one]

theorem frequencyRadius_one (k : Legacy.TorusEndpoint.Frequency 1) :
    Legacy.TorusEndpoint.frequencyRadius k = |(k 0 : ℝ)| := by
  simp [Legacy.TorusEndpoint.frequencyRadius, Real.sqrt_sq_eq_abs]

theorem circle_energyTerm (rho : Legacy.TorusEndpoint.ProbabilityDensity 1)
    (k : Legacy.TorusEndpoint.NonzeroFrequency 1) :
    Legacy.TorusEndpoint.densitySpectralTerm rho k =
      Legacy.D10.CircleEntropy.weight k.val * ‖Legacy.TorusEndpoint.densityFourier rho.value k.val‖ ^ 2 := by
  simp [Legacy.TorusEndpoint.densitySpectralTerm, frequencyRadius_one,
    Legacy.D10.CircleEntropy.weight, div_eq_mul_inv, mul_comm]

/-- Unconditional dimension-one endpoint for every actual finite-entropy density. -/
theorem endpoint_one : Endpoint 1 := by
  intro rho hEntropy
  obtain ⟨hsum, hbound⟩ := Legacy.D10.CircleEntropy.entropy_bound rho hEntropy
  have heq : Legacy.TorusEndpoint.densitySpectralTerm rho =
      (fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 =>
        Legacy.D10.CircleEntropy.weight k.val * ‖Legacy.TorusEndpoint.densityFourier rho.value k.val‖ ^ 2) :=
    funext (circle_energyTerm rho)
  refine ⟨heq ▸ hsum, ?_⟩
  rw [endpointConstant_one]
  unfold fourierEnergy
  rw [heq]
  linarith

theorem normalized_energy {d : ℕ} (rho : Legacy.TorusEndpoint.ProbabilityDensity d) :
    Legacy.TorusEndpoint.densitySpectralEnergy rho =
      fourierEnergy rho / Legacy.TorusEndpoint.endpointSigma d := by
  unfold Legacy.TorusEndpoint.densitySpectralEnergy fourierEnergy
  ring

/-- Heat densities prove the necessary sharpness direction in every positive
dimension without assuming that its endpoint inequality holds. -/
theorem sharpness {d : ℕ} (hd : 0 < d) : Sharpness d := by
  intro C hC
  have hsigma := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hC' : (d : ℝ) < C * Legacy.TorusEndpoint.endpointSigma d := by
    exact (div_lt_iff₀ hsigma).mp hC
  obtain ⟨t, ht, _, hfail⟩ :=
    Legacy.TorusEndpoint.EndpointSharpness.exists_heatDensity_violation hd hC'
  let rho := Legacy.TorusEndpoint.EndpointSharpnessHeat.heatDensity d ht
  obtain ⟨hsum, heq⟩ := Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy_eq_spectral
    hd rho (Legacy.TorusEndpoint.EndpointSharpnessHeat.heatDensity_memLp d ht)
  refine ⟨rho, Legacy.TorusEndpoint.EndpointSharpnessHeat.heatDensity_finiteEntropy d ht,
    hsum, ?_⟩
  change Legacy.TorusEndpoint.densityEntropy rho.value <
    (C * Legacy.TorusEndpoint.endpointSigma d) *
      Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy rho at hfail
  rw [heq, normalized_energy] at hfail
  have hc : (C * Legacy.TorusEndpoint.endpointSigma d) *
      (fourierEnergy rho / Legacy.TorusEndpoint.endpointSigma d) = C * fourierEnergy rho := by
    field_simp [hsigma.ne']
  rwa [hc] at hfail

theorem coefficient_le_endpointConstant {d : ℕ} (hd : 0 < d) (C : ℝ)
    (hbound : ∀ rho : Legacy.TorusEndpoint.ProbabilityDensity d, rho.FiniteEntropy →
      C * fourierEnergy rho ≤ Legacy.TorusEndpoint.densityEntropy rho.value) :
    C ≤ endpointConstant d := by
  by_contra h
  obtain ⟨rho, hEntropy, _, hfail⟩ := sharpness hd C (lt_of_not_ge h)
  exact (not_lt_of_ge (hbound rho hEntropy)) hfail

/-- Dimension one has both endpoint validity and the exact optimal constant. -/
theorem endpoint_one_isGreatest :
    IsGreatest {C : ℝ | ∀ rho : Legacy.TorusEndpoint.ProbabilityDensity 1,
      rho.FiniteEntropy → C * fourierEnergy rho ≤ Legacy.TorusEndpoint.densityEntropy rho.value}
      (1 / 2) := by
  constructor
  · intro rho hEntropy
    simpa only [endpointConstant_one] using (endpoint_one rho hEntropy).2
  · intro C hC
    simpa only [endpointConstant_one] using
      coefficient_le_endpointConstant (by decide : 0 < 1) C hC

end Legacy.BecknerOnofri

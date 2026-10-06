module

public import BecknerOnofri.Paper2.Proofs
public import BecknerOnofri.EntropyMainTheorems
public import BecknerOnofri.ElevenCoexistence
public import BecknerOnofri.ElevenCompetitorEnergy
public import BecknerOnofri.ElevenConditionalEntropy
public import BecknerOnofri.ElevenDefectCorner
public import BecknerOnofri.ElevenPressureCorner
public import BecknerOnofri.ElevenDerivativeJumps
public import BecknerOnofri.ElevenProfileRegularity
public import BecknerOnofri.ElevenTrialConsequences
public import BecknerOnofri.ElevenVariational
public import BecknerOnofri.ElevenUniformHessian
public import BecknerOnofri.ElevenTransitionZeroSet
public import BecknerOnofri.VariationalTransitionQuotient
public import BecknerOnofri.VariationalThresholdGeometry
public import BecknerOnofri.LowDimensionConsequences
public import BecknerOnofri.LowDimensionRaw
public import BecknerOnofri.Kappa

@[expose] public section

/-!
# Named results used by `Solution`

Thin wrappers around the library results that `Solution.lean` assembles into the statements
of `Challenge.lean`.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace BecknerOnofri.Target
open HighDim

theorem eleven_coexistence :
    IsGlobalMinimizer Eleven.globalTransition (uniformDensity 11) ∧
    ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer Eleven.globalTransition ρ ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
      ¬ (ρ.value =ᵐ[torusMeasure 11] (fun _ => 1)) := by
  exact Eleven.coexistence

theorem eleven_competitor_energy (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    ENNReal.ofReal (2*((14475384292906 : ℝ)/10^12)) < spectralEnergy ρ := by
  exact Eleven.competitor_energy ρ hρ

theorem eleven_competitor_entropy (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    entropy ρ < (18011 : ℝ)/1250 := by
  exact Eleven.competitor_entropy ρ hρ

theorem eleven_defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < Eleven.zeroDefectCoefficient ∧
      ∀ A : ℝ, |A - Eleven.zeroDefectCoefficient| < ε →
        coefficientDefect 11 A = (Eleven.defectReal A : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.defectReal Eleven.zeroDefectCoefficient := by
  exact Eleven.defect_corner

theorem eleven_pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = (Eleven.pressureReal β : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.pressureReal Eleven.globalTransition := by
  exact Eleven.pressure_corner

theorem eleven_pressure_derivative_jump : ∃ p : ℝ, 0 < p ∧
    HasDerivWithinAt Eleven.pressureReal 0 (Set.Iio Eleven.globalTransition) Eleven.globalTransition ∧
    HasDerivWithinAt Eleven.pressureReal p (Set.Ioi Eleven.globalTransition) Eleven.globalTransition := by
  exact Eleven.pressure_derivative_jump

theorem eleven_profile_regular :
    ∃ ρ : ProbabilityDensity 11, ρ.value = Eleven.periodizedProfile ∧
      ρ.FiniteEntropy ∧ SmoothOnTorus ρ.value ∧ ∀ x, 0 < ρ.value x := by
  exact Eleven.profile_regular

theorem eleven_spectral_pressure :
    (1/30 : EReal) < pressure 11 (spectralThreshold 11) ∧
      coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) := by
  exact ⟨Eleven.spectral_pressure, Eleven.defect_at_spectral⟩

theorem eleven_transition_interval :
    (3543 : ℝ)/200 < Eleven.globalTransition ∧
    Eleven.globalTransition < 2063/100 ∧
    (2063 : ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 := by
  exact Eleven.transition_interval

theorem eleven_uniform_hessian :
    0 < 1 - Eleven.globalTransition / spectralThreshold 11 ∧
    ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
      (1 - Eleven.globalTransition / spectralThreshold 11) *
          (∫ x, (h x)^2 ∂torusMeasure 11) ≤ Eleven.uniformHessian Eleven.globalTransition h := by
  exact Eleven.uniform_hessian

theorem general_pressure_zero_set (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 ≤ β) :
    pressure d β = 0 ↔ β ≤ VariationalCurves.globalTransition d := by
  exact VariationalCurves.pressure_zero_iff hd β

theorem general_threshold_bounds (d : ℕ) (hd : 0 < d) :
    0 < VariationalCurves.globalTransition d ∧
    VariationalCurves.globalTransition d ≤ min (2*(d:ℝ)) (spectralThreshold d) ∧
    max (collapseCoefficient d) (spectralCoefficient d) ≤ VariationalCurves.zeroDefectCoefficient d := by
  exact ⟨VariationalCurves.transition_positive hd,VariationalCurves.transition_upper_bounds hd,
    VariationalCurves.coefficient_lower_bounds hd⟩

theorem kappa_positive (d : ℕ) (hd : 12 ≤ d) : 0 < kappa d :=
  kappa_pos d hd

theorem low_circle_density (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    ((((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2) := by
  exact LowDimension.circle_density ρ hρ

theorem low_circle_potential (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1-conj a*fourier 1 (x 0)‖+c) := by
  exact LowDimension.circle_potential u hu

theorem low_coefficient_formula (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ := by
  exact LowDimension.coefficient_formula hd hd10 A

theorem low_coefficient_sharp (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) := by
  exact LowDimension.potential_coefficient_sharp hd hd10

theorem low_density_rigidity (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    ((((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1) := by
  exact LowDimension.density_rigidity hd hd10 ρ hρ

theorem low_potential_endpoint (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  exact LowDimension.potential_bound hd hd10 u hu

theorem low_potential_rigidity (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) := by
  exact LowDimension.potential_rigidity hd hd10 u hu

theorem low_pressure_formula (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ := by
  exact LowDimension.pressure_formula hd hd10 β

end BecknerOnofri.Target

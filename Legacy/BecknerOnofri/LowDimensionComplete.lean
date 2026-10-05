import Legacy.BecknerOnofri.CircleEqualityComplete
import Legacy.BecknerOnofri.CollapseDivergence

/-! A single checked proposition collecting the complete low-dimensional
manuscript theorem and its coefficient/pressure consequences. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped ComplexConjugate ENNReal
namespace Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment EndpointPotential PhysicalGreenL2

/-- The statements of the September 16 manuscript for dimensions 1 through 10.
All functions, energies, integrals and suprema are the actual analytic objects.
The equality fields impose only the original Sobolev / finite-entropy domains. -/
structure LowDimensionManuscript : Prop where
  spectralEndpoint : EndpointThroughTen
  potentialBound : ∀ {d : ℕ}, 1≤d → d≤10 → ∀ u : TorusL2 d,
    RealPotential u → Summable (weightedSquare (fourierIsometry d u)) →
    Integrable (fun x => Real.exp ((u x).re-∫ y, (u y).re ∂torusMeasure d)) (torusMeasure d) ∧
      Real.log (centeredPartition u) ≤
        (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u
  densityBound : ∀ {d : ℕ}, 1≤d → d≤10 → ∀ r : ProbabilityDensity d, r.FiniteEntropy →
    Integrable (fun z : Torus d × Torus d =>
      GreenKernelReal.realGreen d (z.1-z.2)*r.value z.1*r.value z.2)
        ((torusMeasure d).prod (torusMeasure d)) ∧
      (d:ℝ)*physicalGreenEnergy r ≤ densityEntropy r.value
  sharpPotential : ∀ {d : ℕ}, 1≤d → d≤10 →
    IsLeast {a : ℝ | ∀ u : TorusL2 d, RealPotential u →
      Summable (weightedSquare (fourierIsometry d u)) →
      Real.log (centeredPartition u) ≤ a*manuscriptEnergy u}
        (1/(4*(d:ℝ)*endpointSymbolConstant d))
  sharpDensity : ∀ {d : ℕ}, 1≤d → d≤10 →
    IsGreatest {C : ℝ | ∀ r : ProbabilityDensity d, r.FiniteEntropy →
      C*physicalGreenEnergy r ≤ densityEntropy r.value} (d:ℝ)
  potentialRigidity : ∀ {d : ℕ}, 2≤d → d≤10 → ∀ u : TorusL2 d,
    RealPotential u → Summable (weightedSquare (fourierIsometry d u)) →
      (Real.log (centeredPartition u) =
        (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u ↔
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => (c:ℂ))
  densityRigidity : ∀ {d : ℕ}, 2≤d → d≤10 → ∀ r : ProbabilityDensity d, r.FiniteEntropy →
    ((d:ℝ)*physicalGreenEnergy r = densityEntropy r.value ↔
      r.value =ᵐ[torusMeasure d] fun _ => 1)
  circlePotential : ∀ u : TorusL2 1,
    RealPotential u → Summable (weightedSquare (fourierIsometry 1 u)) →
      (Real.log (centeredPartition u) =
        (1/(4*(1:ℝ)*endpointSymbolConstant 1))*manuscriptEnergy u ↔
        ∃ a : ℂ, ‖a‖<1 ∧ ∃ c : ℝ,
          u =ᵐ[torusMeasure 1] fun x =>
            ((-2*Real.log ‖1-conj a*fourier 1 (x 0)‖+c : ℝ):ℂ))
  circleDensity : ∀ r : ProbabilityDensity 1, r.FiniteEntropy →
    (physicalGreenEnergy r = densityEntropy r.value ↔
      ∃ a : ℂ, ‖a‖<1 ∧ r.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2)
  greenIdentification : ∀ {d : ℕ}, 1≤d → d≤10 →
    ∀ r : ProbabilityDensity d, r.FiniteEntropy →
      physicalGreenEnergy r = densitySpectralEnergy r
  pressure : ∀ {d : ℕ}, 1≤d → d≤10 → ∀ β : ℝ,
    LowDimensionThresholds.pressure d β = if β≤2*(d:ℝ) then 0 else ∞
  coefficientDefect : ∀ {d : ℕ}, 1≤d → d≤10 → ∀ A : ℝ,
    LowDimensionThresholds.coefficientDefect d A =
      if 1/(4*(d:ℝ)*endpointSymbolConstant d)≤A then 0 else ∞

theorem low_dimension_manuscript : LowDimensionManuscript where
  spectralEndpoint := endpoint_through_ten
  potentialBound := fun hd hd10 _ hr hs => onofri_through_ten hd hd10 hr hs
  densityBound := physical_green_endpoint
  sharpPotential := onofri_physical_coefficient_isLeast
  sharpDensity := physical_green_coefficient_isGreatest
  potentialRigidity := fun hd hd10 _ hr hs => onofri_equality_iff_constant hd hd10 hr hs
  densityRigidity := physical_green_equality_iff_uniform
  circlePotential := fun _ hr hs => CircleEquality.onofri_equality_iff_paper_family hr hs
  circleDensity := CircleEquality.physical_green_equality_iff_paper_family
  greenIdentification := FiniteEnergyGreenIdentification.finiteEntropy_physicalGreen_eq_spectral
  pressure := CollapseDivergence.pressure_formula
  coefficientDefect := CollapseDivergence.coefficientDefect_formula

#print axioms low_dimension_manuscript
end Legacy.BecknerOnofri

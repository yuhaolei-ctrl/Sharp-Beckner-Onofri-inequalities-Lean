module

public import Legacy.BecknerOnofri.EndpointDensityGibbs
public import Legacy.BecknerOnofri.EndpointMaximizerLevel
public import Legacy.BecknerOnofri.EndpointPotentialEquality

@[expose] public section

/-! Actual finite-entropy equality densities and actual Sobolev potential
equality cases correspond through the Gibbs map, including the circle. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.EndpointEqualityCorrespondence
open TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual
open EndpointPotential EndpointMaximizerLevel

theorem exists_potential_equality {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (he : endpointConstant d*fourierEnergy r = densityEntropy r.value) :
    ∃ u : TorusL2 d, Admissible u ∧
      Real.log (partition u) = coefficient d*criticalEnergy u ∧
      r.value =ᵐ[torusMeasure d] gibbsValue u := by
  have hR := rough_of_endpoint hd hE
  have hA := coefficient_pos hd
  have hCoeff : 1/(4*coefficient d) = endpointConstant d := by
    unfold coefficient
    field_simp
  have hL2 := EndpointDensityGibbs.memLp_two_of_equality hd hE r hr he
  have hm := equality_density_maximizer hE hCoeff r he.symm
  let u := dualPotential (coefficient d) r hL2
  have hu := dualPotential_admissible hd (coefficient d) r hL2
  have huM := (density_maximizer_dual hd hR hA r hL2 hm).2
  have hzero := maximizer_functional_zero hd hE hR hA hCoeff hu huM
  exact ⟨u, hu, sub_eq_zero.mp hzero, density_maximizer_gibbs hd hR hA r hL2 hm⟩

#print axioms exists_potential_equality
end Legacy.BecknerOnofri.EndpointEqualityCorrespondence

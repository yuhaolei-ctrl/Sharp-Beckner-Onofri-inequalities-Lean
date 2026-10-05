module

public import BecknerOnofri.FullBranchAssembly
public import BecknerOnofri.PhysicalNormalCoercivity
public import BecknerOnofri.NumericalOnsetReduction

@[expose] public section

/-! Completion of the analytic branch argument. The exact full branch theorem
has the same single explicit d=12 numerical obligation as the endpoint theorem.
No numerical premise is hidden in definitions or asserted as an axiom. -/
noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim

/-- Every actual physical branch point near onset has the complete raw-domain
Morse--Bott Hessian, including strict normal H^(d/2) coercivity. -/
theorem physical_hessian_properties {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      FullBranchAssembly.HessianProperties β (DiagonalScalarBranch.physicalPotential hd β) := by
  filter_upwards [FullBranchHessian.physical_hessian_nonpos_kernel hd,
    PhysicalNormalCoercivity.physical_normalCoercivity hd] with β hh hn
  exact ⟨fun h hreg hm => (hh h hreg hm).1,
    fun h hreg hm => (hh h hreg hm).2,hn⟩

/-- The full trusted branch and density-orbit assertion follows from the
actual endpoint inequality and its equality classification. -/
theorem full_branch_onset_of_endpoint {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    FullBranchOnset d :=
  FullBranchAssembly.full_branch_onset_of_hessian hd hEndpoint hRigidity (physical_hessian_properties hd)

/-- All content of the exact full-branch target, conditional on the sole
unproved dimension-twelve numerical-neighborhood proposition. -/
theorem full_branch_onset_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) : FullBranchOnset d :=
  full_branch_onset_of_endpoint hd (legacy_endpoint_of_twelve_neighborhood hnum hd)
    (legacy_rigidity_of_twelve_neighborhood hnum hd)

#print axioms physical_hessian_properties
#print axioms full_branch_onset_of_endpoint
#print axioms full_branch_onset_of_twelve_neighborhood
end BecknerOnofri.HighDim

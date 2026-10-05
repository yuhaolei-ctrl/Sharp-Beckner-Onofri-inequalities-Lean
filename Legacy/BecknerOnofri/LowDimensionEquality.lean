import Legacy.BecknerOnofri.EndpointEqualityL2
import Legacy.BecknerOnofri.EndpointDensityGibbs
import Legacy.BecknerOnofri.LowDimensionPotentialEquality

/-! Unconditional equality classification for all finite-entropy densities
in dimensions two through ten. L2 regularity is deduced from equality using
finite Fourier potentials and the vanishing Young gap, then compact endpoint
selection and the strict mixed-profile estimate force uniformity. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri

theorem endpoint_uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (he : endpointConstant d*fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure d] (fun _ => 1) :=
  EndpointEqualityL2.uniform_of_equality hd2 hd10 r
    (EndpointDensityGibbs.memLp_two_of_equality (by omega)
      (endpoint_through_ten d (by omega) hd10) r hr he) he

theorem endpoint_equality_iff_uniform {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    endpointConstant d*fourierEnergy r = densityEntropy r.value ↔
      r.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  refine ⟨endpoint_uniform_of_equality hd2 hd10 r hr, ?_⟩
  intro he
  have hEnt := (EntropyVariationalEquality.entropy_eq_zero_iff r hr).mpr he
  apply le_antisymm (endpoint_through_ten d (by omega) hd10 r hr).2
  rw [hEnt]
  exact mul_nonneg (EndpointPotential.endpointConstant_pos (by omega : 0 < d)).le
    (SteinerEndpointReduction.energy_nonneg r)

theorem endpoint_strict_of_nonuniform {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (hne : ¬r.value =ᵐ[torusMeasure d] (fun _ => 1)) :
    endpointConstant d*fourierEnergy r < densityEntropy r.value := by
  apply lt_of_le_of_ne (endpoint_through_ten d (by omega) hd10 r hr).2
  exact fun he => hne (endpoint_uniform_of_equality hd2 hd10 r hr he)

theorem densityEqualityRigidity {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    EndpointPotential.DensityEqualityRigidity d :=
  endpoint_uniform_of_equality hd2 hd10

#print axioms endpoint_uniform_of_equality
#print axioms endpoint_equality_iff_uniform
#print axioms endpoint_strict_of_nonuniform
end Legacy.BecknerOnofri

module

public import Legacy.BecknerOnofri.LowDimensionEquality
public import Legacy.TorusEndpoint.PhysicalGreenFiniteEnergy

@[expose] public section

/-! The actual singular Green-interaction version of the low-dimensional
endpoint. Integrability of the interaction is a conclusion for every density
of finite entropy, and its exact optimal coefficient and rigidity follow. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri
open GreenKernelReal PhysicalGreenL2 PhysicalGreenFiniteEnergy

theorem physical_green_endpoint {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    Integrable (fun z : Torus d × Torus d =>
      realGreen d (z.1-z.2)*r.value z.1*r.value z.2)
      ((torusMeasure d).prod (torusMeasure d)) ∧
      (d:ℝ)*physicalGreenEnergy r ≤ densityEntropy r.value := by
  obtain ⟨hi, hle⟩ := physicalGreen_integrable_and_le_spectral (by omega) r
    (endpoint_through_ten d hd hd10 r hr).1
  exact ⟨hi, (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg d)).trans
    (normalized_entropy_endpoint hd hd10 r hr)⟩

theorem physical_green_coefficient_isGreatest {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsGreatest {C : ℝ | ∀ r : ProbabilityDensity d, r.FiniteEntropy →
      C*physicalGreenEnergy r ≤ densityEntropy r.value} (d:ℝ) :=
  ⟨fun r hr => (physical_green_endpoint hd hd10 r hr).2,
    fun C hC => EndpointSharpness.coefficient_le_dimension_of_uniform_bound (by omega) C hC⟩

theorem physical_green_equality_iff_uniform {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    (d:ℝ)*physicalGreenEnergy r = densityEntropy r.value ↔
      r.value =ᵐ[torusMeasure d] fun _ => 1 := by
  have hscale : endpointConstant d*fourierEnergy r = (d:ℝ)*densitySpectralEnergy r := by
    rw [normalized_energy]
    unfold endpointConstant
    ring
  constructor
  · intro he
    have hle := (physicalGreen_integrable_and_le_spectral (by omega) r
      (endpoint_through_ten d (by omega) hd10 r hr).1).2
    have hspec : (d:ℝ)*densitySpectralEnergy r = densityEntropy r.value :=
      le_antisymm (normalized_entropy_endpoint (by omega) hd10 r hr)
        (he ▸ mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg d))
    exact endpoint_uniform_of_equality hd2 hd10 r hr (hscale.trans hspec)
  · intro he
    have hL2 : MemLp r.value 2 (torusMeasure d) := (memLp_const (1:ℝ)).ae_eq he.symm
    rw [(physicalGreenEnergy_eq_spectral (by omega) r hL2).2, ← hscale]
    exact (endpoint_equality_iff_uniform hd2 hd10 r hr).mpr he

#print axioms physical_green_endpoint
#print axioms physical_green_coefficient_isGreatest
#print axioms physical_green_equality_iff_uniform
end Legacy.BecknerOnofri

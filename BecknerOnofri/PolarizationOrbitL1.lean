import BecknerOnofri.PolarizationOrbitDistribution
import BecknerOnofri.DistributionL1Limit

/-! Actual probability densities, entropy and nonuniformity in the L1 closure
of their finite polarization orbit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.PolarizationL1

theorem orbit_l1_identDistrib {d : ℕ} {f h : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hh : Integrable h (torusMeasure d))
    {g : ℕ → Torus d → ℝ} (hg : ∀ n,Orbit f (g n))
    (hc : Tendsto (fun n => ∫ x,‖g n x-h x‖ ∂torusMeasure d) atTop (𝓝 0)) :
    IdentDistrib h f (torusMeasure d) (torusMeasure d) :=
  DistributionLimit.identDistrib_of_l1 (fun n => (hg n).identDistrib hf.aestronglyMeasurable) hf hh hc

def orbitLimitDensity {d : ℕ} (ρ : ProbabilityDensity d) (h : Torus d → ℝ)
    (hh : Integrable h (torusMeasure d)) (g : ℕ → Torus d → ℝ)
    (hg : ∀ n,Orbit ρ.value (g n))
    (hc : Tendsto (fun n => ∫ x,‖g n x-h x‖ ∂torusMeasure d) atTop (𝓝 0)) :
    ProbabilityDensity d where
  value := h
  integrable := hh
  nonneg := (orbit_l1_identDistrib ρ.integrable hh hg hc).symm.ae_snd
    (by exact measurableSet_Ici) ρ.nonneg
  mass := (orbit_l1_identDistrib ρ.integrable hh hg hc).integral_eq.trans ρ.mass

/-- All entropy is preserved even when only L1 convergence is supplied. -/
theorem orbitLimitDensity_entropy {d : ℕ} (ρ : ProbabilityDensity d) (h : Torus d → ℝ)
    (hh : Integrable h (torusMeasure d)) (g : ℕ → Torus d → ℝ)
    (hg : ∀ n,Orbit ρ.value (g n))
    (hc : Tendsto (fun n => ∫ x,‖g n x-h x‖ ∂torusMeasure d) atTop (𝓝 0))
    (hE : ρ.FiniteEntropy) :
    (orbitLimitDensity ρ h hh g hg hc).FiniteEntropy ∧
    densityEntropy (orbitLimitDensity ρ h hh g hg hc).value=densityEntropy ρ.value := by
  have he := (orbit_l1_identDistrib ρ.integrable hh hg hc).comp Real.continuous_mul_log.measurable
  exact ⟨he.integrable_iff.mpr hE,he.integral_eq⟩

theorem orbitLimitDensity_nonuniform {d : ℕ} (ρ : ProbabilityDensity d) (h : Torus d → ℝ)
    (hh : Integrable h (torusMeasure d)) (g : ℕ → Torus d → ℝ)
    (hg : ∀ n,Orbit ρ.value (g n))
    (hc : Tendsto (fun n => ∫ x,‖g n x-h x‖ ∂torusMeasure d) atTop (𝓝 0))
    (hn : ¬ρ.value=ᵐ[torusMeasure d] (fun _ => 1)) :
    ¬(orbitLimitDensity ρ h hh g hg hc).value=ᵐ[torusMeasure d] (fun _ => 1) := by
  intro he
  apply hn
  exact (orbit_l1_identDistrib ρ.integrable hh hg hc).ae_snd (measurableSet_singleton 1) he

#print axioms orbit_l1_identDistrib
#print axioms orbitLimitDensity_entropy
#print axioms orbitLimitDensity_nonuniform
end BecknerOnofri.PolarizationL1

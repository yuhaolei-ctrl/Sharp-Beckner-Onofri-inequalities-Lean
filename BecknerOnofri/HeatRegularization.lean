module

public import BecknerOnofri.HeatDefinitions
public import BecknerOnofri.HeatDensitySmooth
public import BecknerOnofri.FiniteEntropyPhysical

@[expose] public section

/-! Bridge the source's physical heat time to the theta parameter used
in the Fourier construction, then state regularity and interaction convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim

lemma physicalHeatKernel_eq {d : ℕ} (t : ℝ) (x : Torus d) :
    physicalHeatKernel d t x = Legacy.BecknerOnofri.HeatDensityApproximation.heatKernel (4*Real.pi*t) x := by
  unfold physicalHeatKernel Legacy.BecknerOnofri.HeatDensityApproximation.heatKernel
    Legacy.TorusEndpoint.TorusHeatPositivity.torusTheta
  congr 1
  apply tsum_congr
  intro k
  congr 2
  ring

lemma heatRegularization_eq {d : ℕ} (ρ : ProbabilityDensity d) (t : ℝ) :
    heatRegularization ρ t = Legacy.BecknerOnofri.HeatDensityApproximation.heatValue (Bridge.density ρ) (4*Real.pi*t) := by
  funext x
  unfold heatRegularization Legacy.BecknerOnofri.HeatDensityApproximation.heatValue
  simp only [physicalHeatKernel_eq]
  rfl

theorem heatRegularization_regular {d : ℕ} (ρ : ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) :
    ∃ η : ProbabilityDensity d, η.value = heatRegularization ρ t ∧ η.FiniteEntropy ∧
      SmoothOnTorus η.value ∧ ∀ x, 0 < η.value x := by
  have ht' : 0 < 4*Real.pi*t := by positivity
  let r := Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity (Bridge.density ρ) ht'
  let η : ProbabilityDensity d := ⟨r.value,r.nonneg,r.integrable,r.mass⟩
  refine ⟨η, (heatRegularization_eq ρ t).symm,
    Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_finiteEntropy _ ht',
    HeatSmooth.heatValue_smooth _ ht', ?_⟩
  exact Legacy.BecknerOnofri.HeatDensityApproximation.heatValue_pos _ ht'

theorem heatRegularization_interaction_limit {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ∫ y,
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
      heatRegularization ρ (t n) x*heatRegularization ρ (t n) y ∂torusMeasure d ∂torusMeasure d)
      atTop (𝓝 (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
        ρ.value x*ρ.value y ∂torusMeasure d ∂torusMeasure d)) := by
  have ht' (n : ℕ) : 0 < 4*Real.pi*t n := mul_pos (by positivity) (ht n)
  have hlim : Tendsto (fun n => 4*Real.pi*t n) atTop (𝓝 0) := by
    simpa using ht0.const_mul (4*Real.pi)
  have h := FiniteEntropyPhysical.heat_interaction_tendsto hd (Bridge.density ρ) hρ _ ht' hlim
  simp only [heatRegularization_eq]
  exact h

#print axioms heatRegularization_regular
#print axioms heatRegularization_interaction_limit
end BecknerOnofri.HighDim

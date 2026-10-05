import BecknerOnofri.PolarizationOrbitCompact
import BecknerOnofri.PolarizationUniformContinuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Sequences

/-! The uniform orbit closure is invariant under every genuine polarization. -/
noncomputable section
open scoped BoundedContinuousFunction
open Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization

lemma closure_lipschitz {d : ℕ} {f : Torus d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit f)) :
    LipschitzWith K g := by
  have hc : IsClosed {g : Torus d →ᵇ ℝ | LipschitzWith K g} :=
    (isClosed_setOf_lipschitzWith (α := Torus d) (β := ℝ) K).preimage
      (BoundedContinuousFunction.continuous_coe (α := Torus d) (β := ℝ))
  apply closure_minimal (s := boundedOrbit f) (t := {g : Torus d →ᵇ ℝ | LipschitzWith K g}) ?_ hc hg
  intro h hh
  exact Orbit.lipschitz hh hf

def boundedPolarize {d : ℕ} (i : Fin d) (a : ℝ) (g : Torus d →ᵇ ℝ) {K : ℝ≥0}
    (hg : LipschitzWith K g) : Torus d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨polarize i a g,(polarize_lipschitz i a hg).continuous⟩

theorem closure_polarize {d : ℕ} {f : Torus d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit f))
    (i : Fin d) (a : ℝ) :
    boundedPolarize i a g (closure_lipschitz hf hg)∈closure (boundedOrbit f) := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
  have huL (n : ℕ) : LipschitzWith K (u n) := Orbit.lipschitz (hu n) hf
  let v : ℕ → Torus d →ᵇ ℝ := fun n => boundedPolarize i a (u n) (huL n)
  have hv (n : ℕ) : v n∈boundedOrbit f := Orbit.step (hu n) i a
  have htv : Tendsto v atTop (𝓝 (boundedPolarize i a g (closure_lipschitz hf hg))) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact polarize_tendstoUniformly i a (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu)
  exact mem_closure_of_tendsto htv (Filter.Eventually.of_forall hv)

#print axioms closure_polarize
end BecknerOnofri.PolarizationL1

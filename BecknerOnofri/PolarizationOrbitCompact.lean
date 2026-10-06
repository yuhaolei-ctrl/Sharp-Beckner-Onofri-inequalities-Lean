module

public import BecknerOnofri.PolarizationLipschitz
public import BecknerOnofri.PolarizationOrbitDistribution
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

@[expose] public section

/-! The actual polarization orbit of a Lipschitz function has compact uniform
closure, as used before maximizing the strict cosine moment. -/
noncomputable section
open scoped BoundedContinuousFunction
open scoped NNReal
open Set Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization

theorem Orbit.lipschitz {d : ℕ} {f g : Torus d → ℝ} {K : ℝ≥0}
    (h : Orbit f g) (hf : LipschitzWith K f) : LipschitzWith K g := by
  induction h with
  | refl => exact hf
  | step hg i a ih => exact polarize_lipschitz i a ih

theorem Orbit.range_bound {d : ℕ} {f g : Torus d → ℝ} {C : ℝ}
    (h : Orbit f g) (hf : ∀ x,‖f x‖≤C) : ∀ x,‖g x‖≤C := by
  induction h with
  | refl => exact hf
  | step hg i a ih =>
    intro x
    rcases polarize_value_or_reflected i a _ x with he | he <;> rw [he] <;> exact ih _

def boundedOrbit {d : ℕ} (f : Torus d → ℝ) : Set (Torus d →ᵇ ℝ) :=
  {g | Orbit f g}

/-- No compactness premise is assumed: the original Lipschitz bound and
supremum bound persist through all finite polarizations. -/
theorem compact_orbit_closure {d : ℕ} (f : Torus d → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) {C : ℝ} (hC : ∀ x,‖f x‖≤C) :
    IsCompact (closure (boundedOrbit f)) := by
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-C) C) isCompact_Icc
  · intro g x hg
    have ho : Orbit f g := hg
    have h := (ho.range_bound hC) x
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using h)
  · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (K : ℝ)*r)
    · have hc : Continuous (fun r : ℝ => (K : ℝ)*r) := continuous_const.mul continuous_id
      simpa only [mul_zero] using hc.tendsto 0
    · intro x y g
      have ho : Orbit f g.val := g.property
      exact (ho.lipschitz hf).dist_le_mul x y

#print axioms compact_orbit_closure
end BecknerOnofri.PolarizationL1

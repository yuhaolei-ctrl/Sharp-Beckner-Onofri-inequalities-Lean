import BecknerOnofri.PolarizationOrbitDistribution
import BecknerOnofri.DistributionL1Limit
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

noncomputable section
open MeasureTheory Filter ProbabilityTheory Legacy.TorusEndpoint
open scoped Topology BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1

/-- Uniform convergence of bounded continuous functions implies convergence
in the concrete normalized Haar L1 metric. -/
theorem bounded_tendsto_l1 {d : ℕ} {ι : Type*} {l : Filter ι}
    {u : ι → Torus d →ᵇ ℝ} {g : Torus d →ᵇ ℝ} (h : Tendsto u l (𝓝 g)) :
    Tendsto (fun n => ∫ x,‖u n x-g x‖ ∂torusMeasure d) l (𝓝 0) := by
  have hb (n : ι) : (∫ x,‖u n x-g x‖ ∂torusMeasure d)≤dist (u n) g := by
    have hi : Integrable (fun x => ‖u n x-g x‖) (torusMeasure d) :=
      ((u n).integrable _ |>.sub (g.integrable _)).norm
    have hh := integral_mono hi (integrable_const (dist (u n) g))
      (fun x => by simpa only [dist_eq_norm] using BoundedContinuousFunction.dist_coe_le_dist (f := u n) (g := g) x)
    simpa using hh
  have ht : Tendsto (fun n => dist (u n) g) l (𝓝 0) := by
    simpa only [dist_self] using h.dist (tendsto_const_nhds (x := g))
  exact squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _)) hb ht

/-- The uniform closure of a genuine polarization orbit retains the entire
original distribution, not only its integral. -/
theorem bounded_orbit_limit_identDistrib {d : ℕ} {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) {u : ℕ → Torus d →ᵇ ℝ} {g : Torus d →ᵇ ℝ}
    (hu : ∀ n,Orbit f (u n)) (h : Tendsto u atTop (𝓝 g)) :
    IdentDistrib g f (torusMeasure d) (torusMeasure d) :=
  DistributionLimit.identDistrib_of_l1 (fun n => (hu n).identDistrib hf.aestronglyMeasurable)
    hf (g.integrable _) (bounded_tendsto_l1 h)

#print axioms bounded_tendsto_l1
#print axioms bounded_orbit_limit_identDistrib
end BecknerOnofri.PolarizationL1

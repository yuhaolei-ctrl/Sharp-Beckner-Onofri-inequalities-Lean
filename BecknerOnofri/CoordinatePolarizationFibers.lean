import BecknerOnofri.PolarizationOrbitDistribution
import BecknerOnofri.EntropyShearer.L1Marginal

/-! Single-coordinate polarizations preserve each circle fiber's full
 distribution. This is stronger than global equimeasurability and is needed
 to identify canonical successive coordinate rearrangements. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri.CoordinatePolarization

/-- A complete circle fiber, with the other coordinates fixed. -/
def fiber {d : ℕ} (i : Fin d) (f : Torus d → ℝ) (x : Torus d) : Torus 1 → ℝ :=
  fun z => f (Function.update x i (z 0))

lemma reflection_update {d : ℕ} (i : Fin d) (a : ℝ) (x : Torus d) (z : Torus 1) :
    reflection i a (Function.update x i (z 0)) =
      Function.update x i ((reflection (0 : Fin 1) a z) 0) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [reflection]
  · simp [reflection,hj]

lemma fiber_polarize {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) (x : Torus d) :
    fiber i (polarize i a f) x = polarize 0 a (fiber i f x) := by
  funext z
  have hh : Function.update x i (z 0) ∈ halfTorus i a ↔ z ∈ halfTorus 0 a := by
    simp only [halfTorus,mem_setOf_eq,Function.update_self]
  simp only [fiber,polarize,reflection_update]
  rw [hh]

lemma fiber_continuous {d : ℕ} (i : Fin d) {f : Torus d → ℝ}
    (hf : Continuous f) (x : Torus d) : Continuous (fiber i f x) :=
  hf.comp (continuous_const.update i (continuous_apply 0))

/-- Finite polarizations restricted to the specified coordinate. -/
inductive Orbit {d : ℕ} (i : Fin d) (f : Torus d → ℝ) : (Torus d → ℝ) → Prop
  | refl : Orbit i f f
  | step {g : Torus d → ℝ} : Orbit i f g → (a : ℝ) → Orbit i f (polarize i a g)

theorem Orbit.global {d : ℕ} {i : Fin d} {f g : Torus d → ℝ} (h : Orbit i f g) :
    PolarizationL1.Orbit f g := by
  induction h with
  | refl => exact .refl
  | step hg a ih => exact .step ih i a

theorem Orbit.fiber_orbit {d : ℕ} {i : Fin d} {f g : Torus d → ℝ} (h : Orbit i f g) (x : Torus d) :
    PolarizationL1.Orbit (fiber i f x) (fiber i g x) := by
  induction h with
  | refl => exact .refl
  | step hg a ih =>
    rw [fiber_polarize]
    exact .step ih 0 a

theorem Orbit.fiber_identDistrib {d : ℕ} {i : Fin d} {f g : Torus d → ℝ}
    (h : Orbit i f g) (hf : Continuous f) (x : Torus d) :
    IdentDistrib (fiber i g x) (fiber i f x) (torusMeasure 1) (torusMeasure 1) :=
  (h.fiber_orbit x).identDistrib (fiber_continuous i hf x).aestronglyMeasurable

/-- Uniform orbit limits preserve every fiber distribution, not merely the
ambient distribution. No symmetry or optimality premise is needed here. -/
theorem orbit_uniform_limit_fiber_identDistrib {d : ℕ} {i : Fin d}
    {f g : Torus d → ℝ} (hf : Continuous f) {u : ℕ → Torus d → ℝ}
    (hu : ∀ n, Orbit i f (u n)) (ht : TendstoUniformly u g atTop) (x : Torus d) :
    IdentDistrib (fiber i g x) (fiber i f x) (torusMeasure 1) (torusMeasure 1) := by
  have hD (n : ℕ) := (hu n).fiber_identDistrib hf x
  apply DistributionLimit.identDistrib_of_tendstoInMeasure hD
  apply tendstoInMeasure_of_tendsto_ae (fun n => (hD n).aestronglyMeasurable_fst)
  exact Eventually.of_forall (fun z => ht.tendsto_at (Function.update x i (z 0)))

#print axioms orbit_uniform_limit_fiber_identDistrib
#print axioms Orbit.fiber_identDistrib
end BecknerOnofri.CoordinateRearrangement

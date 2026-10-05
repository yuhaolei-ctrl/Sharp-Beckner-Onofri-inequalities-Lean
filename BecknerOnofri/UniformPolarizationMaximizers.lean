import BecknerOnofri.PrescribedPolarizationOrbit
import BecknerOnofri.PolarizationOrbitClosure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Uniform orbit limits of a prescribed optimizer remain actual optimizers,
by the continuous embedding into L2 and the proved closed optimizer set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Legacy.TorusEndpoint
open scoped Topology BoundedContinuousFunction
namespace BecknerOnofri.PrescribedPolarization
open Legacy.BecknerOnofri GibbsL2Continuity CoordinatePolarization SubcriticalDensityCompactness
open PolarizationL2

lemma rawOrbit_memLp {d : ℕ} {f g : Torus d → ℝ} (h : PolarizationL1.Orbit f g)
    (hf : MemLp f 2 (torusMeasure d)) : MemLp g 2 (torusMeasure d) := by
  induction h with
  | refl => exact hf
  | step hg i a ih => exact polarize_memLp_two i a ih

lemma rawOrbit_toLp {d : ℕ} {f g : Torus d → ℝ} (h : PolarizationL1.Orbit f g)
    (hf : MemLp f 2 (torusMeasure d)) :
    Orbit (hf.toLp f) ((rawOrbit_memLp h hf).toLp g) := by
  induction h with
  | refl => exact .refl
  | step hg i a ih =>
    rw [← polarizeLp_toLp i a (rawOrbit_memLp hg hf)]
    exact .step ih i a

lemma bounded_toLp_eq {d : ℕ} (g : Torus d →ᵇ ℝ) (hg : MemLp g 2 (torusMeasure d)) :
    BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ g=hg.toLp g := by
  apply Lp.ext
  exact (BoundedContinuousFunction.coeFn_toLp 2 (torusMeasure d) ℝ g).trans hg.coeFn_toLp.symm

theorem uniformClosure_mem_lpClosure {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) {g : Torus d →ᵇ ℝ}
    (hg : g∈closure (PolarizationL1.boundedOrbit f)) :
    BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ g∈orbitClosure (hf.toLp f) := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
  apply mem_closure_of_tendsto
    ((BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ).continuous.tendsto g |>.comp htu)
  apply Eventually.of_forall
  intro n
  change Orbit (hf.toLp f) (BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ (u n))
  rw [bounded_toLp_eq (u n) (rawOrbit_memLp (hu n) hf)]
  exact rawOrbit_toLp (hu n) hf

theorem uniformClosure_mem_maximizers {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d)<A) {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hmax : hf.toLp f∈densityMaximizers d A)
    {g : Torus d →ᵇ ℝ} (hg : g∈closure (PolarizationL1.boundedOrbit f)) :
    BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ g∈densityMaximizers d A :=
  closure_subset_maximizers hd hA hmax (uniformClosure_mem_lpClosure hf hg)

#print axioms uniformClosure_mem_maximizers
end BecknerOnofri.PrescribedPolarization

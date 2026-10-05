import BecknerOnofri.PolarizationLpContinuity
import BecknerOnofri.PolarizationOrbitDistribution
import Legacy.BecknerOnofri.GreenPolarization
import Legacy.BecknerOnofri.SubcriticalDensityCompactness
import Legacy.BecknerOnofri.PolarizationContinuous
import Mathlib.Topology.Sequences

/-! The closure of the polarization orbit of a prescribed L2 density
maximizer is compact, polarization invariant and equimeasurable with it. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.PrescribedPolarization
open Legacy.BecknerOnofri CoordinatePolarization GibbsL2Continuity
open SubcriticalPrimalDual SubcriticalDensityCompactness PolarizationL2

inductive Orbit {d : ℕ} (f : DensityL2 d) : DensityL2 d → Prop
  | refl : Orbit f f
  | step {g : DensityL2 d} : Orbit f g → (i : Fin d) → (a : ℝ) → Orbit f (polarizeLp i a g)

def orbitClosure {d : ℕ} (f : DensityL2 d) : Set (DensityL2 d) := closure {g | Orbit f g}

theorem polarizeLp_toLp {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    polarizeLp i a (hf.toLp f) = (polarize_memLp_two i a hf).toLp (polarize i a f) := by
  apply Lp.ext
  exact (polarizeLp_ae i a (hf.toLp f)).trans
    ((polarize_congr_ae i a hf.coeFn_toLp).trans (MemLp.coeFn_toLp _).symm)

theorem Orbit.identDistrib {d : ℕ} {f g : DensityL2 d} (h : Orbit f g) :
    IdentDistrib (g : Torus d → ℝ) (f : Torus d → ℝ) (torusMeasure d) (torusMeasure d) := by
  induction h with
  | refl => exact IdentDistrib.refl (Lp.aestronglyMeasurable f).aemeasurable
  | step hg i a ih =>
    exact (IdentDistrib.of_ae_eq (Lp.aestronglyMeasurable _).aemeasurable
      (polarizeLp_ae i a _)).trans
      ((PolarizationL1.polarize_identDistrib i a (Lp.aestronglyMeasurable _)).trans ih)

theorem closure_identDistrib {d : ℕ} {f g : DensityL2 d} (h : g ∈ orbitClosure f) :
    IdentDistrib (g : Torus d → ℝ) (f : Torus d → ℝ) (torusMeasure d) (torusMeasure d) := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp h
  exact DistributionLimit.identDistrib_of_tendstoInMeasure
    (fun n => (hu n).identDistrib) (tendstoInMeasure_of_tendsto_Lp ht)

theorem polarizeLp_maps_closure {d : ℕ} (f : DensityL2 d) (i : Fin d) (a : ℝ) :
    MapsTo (polarizeLp i a) (orbitClosure f) (orbitClosure f) :=
  (show MapsTo (polarizeLp i a) {g | Orbit f g} {g | Orbit f g} from
    fun _ hg => Orbit.step hg i a).closure (polarizeLp_lipschitz i a).continuous

theorem polarizeLp_mem_maximizers {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {f : DensityL2 d} (hf : f ∈ densityMaximizers d A) (i : Fin d) (a : ℝ) :
    polarizeLp i a f ∈ densityMaximizers d A := by
  obtain ⟨r, hr, rfl, hmax⟩ := hf
  rw [polarizeLp_toLp i a hr]
  exact ⟨density i a r, density_memLp_two i a hr, rfl,
    (rearranged_density_maximizer hA r (density i a r) (density_memLp_two i a hr) hmax
      (density_entropy i a (PhysicalGreenL2.finiteEntropy_of_memLp r hr))
      (fourierEnergy_polarize_le hd i a r hr)).2⟩

theorem orbit_mem_maximizers {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {f g : DensityL2 d} (hf : f ∈ densityMaximizers d A) (hg : Orbit f g) :
    g ∈ densityMaximizers d A := by
  induction hg with
  | refl => exact hf
  | step hg i a ih => exact polarizeLp_mem_maximizers hd hA ih i a

theorem closure_subset_maximizers {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) {f : DensityL2 d}
    (hf : f ∈ densityMaximizers d A) : orbitClosure f ⊆ densityMaximizers d A := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  exact closure_minimal (fun _ hg => orbit_mem_maximizers hd hA0 hf hg)
    (densityMaximizers_compact_nonempty hd hA).1.isClosed

theorem orbitClosure_isCompact {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) {f : DensityL2 d}
    (hf : f ∈ densityMaximizers d A) : IsCompact (orbitClosure f) :=
  (densityMaximizers_compact_nonempty hd hA).1.of_isClosed_subset isClosed_closure
    (closure_subset_maximizers hd hA hf)

theorem exists_maximal_moment_in_orbit {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) {f : DensityL2 d}
    (hf : f ∈ densityMaximizers d A) (L : DensityL2 d → ℝ) (hL : Continuous L) :
    ∃ g ∈ orbitClosure f, ∀ q ∈ orbitClosure f, L q ≤ L g :=
  (orbitClosure_isCompact hd hA hf).exists_isMaxOn ⟨f, subset_closure Orbit.refl⟩ hL.continuousOn

#print axioms closure_identDistrib
#print axioms exists_maximal_moment_in_orbit
end BecknerOnofri.PrescribedPolarization

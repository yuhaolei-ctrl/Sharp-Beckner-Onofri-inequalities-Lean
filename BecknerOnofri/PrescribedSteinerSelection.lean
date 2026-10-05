import BecknerOnofri.PrescribedPolarizationOrbit
import Legacy.BecknerOnofri.SteinerSelection

/-! Equimeasurable selection within the orbit closure of a prescribed
maximizer. This does not identify the result with the finite successive
canonical fiber rearrangements in the manuscript. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.PrescribedPolarization
open Legacy.BecknerOnofri CoordinatePolarization GibbsL2Continuity
open SubcriticalPrimalDual SubcriticalDensityCompactness PolarizationL2 PolarizationSelection
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier WienerFourier

theorem exists_fixed_prescribed_maximizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d))
    (hmax : ∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
      densityFunctional A s ≤ densityFunctional A r) :
    ∃ q : ProbabilityDensity d, ∃ hq : MemLp q.value 2 (torusMeasure d),
      hq.toLp q.value ∈ orbitClosure (hr.toLp r.value) ∧
      IdentDistrib q.value r.value (torusMeasure d) (torusMeasure d) ∧
      (∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
        densityFunctional A s ≤ densityFunctional A q) ∧
      OriginPolarizationInvariant q.value := by
  let w := CosineMomentWeight.weight d
  have hw := CosineMomentWeight.weight_memLp d
  let L : DensityL2 d → ℝ := fun f => inner ℝ (hw.toLp w) f
  have hL : Continuous L := by fun_prop
  have hrm : hr.toLp r.value ∈ densityMaximizers d A := ⟨r,hr,rfl,hmax⟩
  obtain ⟨g,hg,hm⟩ := exists_maximal_moment_in_orbit hd hA hrm L hL
  obtain ⟨q,hq,rfl,hqm⟩ := closure_subset_maximizers hd hA hrm hg
  refine ⟨q,hq,hg,?_,hqm,?_⟩
  · exact (IdentDistrib.of_ae_eq hq.aestronglyMeasurable.aemeasurable hq.coeFn_toLp.symm).trans
      ((closure_identDistrib hg).trans
        (IdentDistrib.of_ae_eq (Lp.aestronglyMeasurable _).aemeasurable hr.coeFn_toLp))
  · intro i a ha ha0
    have hs := CosineMomentWeight.weight_strict i ha ha0
    have hupper := hm _ (polarizeLp_maps_closure _ i a hg)
    rw [polarizeLp_toLp i a hq] at hupper
    change inner ℝ (hw.toLp w) ((polarize_memLp_two i a hq).toLp (polarize i a q.value)) ≤
      inner ℝ (hw.toLp w) (hq.toLp q.value) at hupper
    rw [inner_toLp_eq_moment _ hw,inner_toLp_eq_moment hq hw] at hupper
    have hmono (x : Torus d) (hx : x∈halfTorus i a) : w (reflection i a x)≤w x := by
      by_cases he : reflection i a x=x
      · rw [he]
      · exact (hs x hx he).le
    exact polarize_ae_eq_of_moment_eq i a hq hw hs
      (le_antisymm (moment_polarize_le i a hq hw hmono) hupper)

/-- The selected actual Euler density has the prescribed distribution, entropy
and maximum value; nonuniformity is retained. -/
theorem exists_equimeasurable_steiner_maximizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d))
    (hmax : ∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
      densityFunctional A s ≤ densityFunctional A r) :
    ∃ u : TorusL2 d, Admissible u ∧
      functional A u = densityFunctional A r ∧
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) ∧
      IdentDistrib (smoothGibbsValue u) r.value (torusMeasure d) (torusMeasure d) ∧
      densityEntropy (smoothGibbsValue u) = densityEntropy r.value ∧
      SteinerSelection.Steiner (smoothGibbsValue u) ∧
      SteinerSelection.Steiner (fun x => (representative u x).re) ∧
      (¬ r.value=ᵐ[torusMeasure d] (fun _ => 1) →
        ¬ smoothGibbsValue u=ᵐ[torusMeasure d] (fun _ => 1)) := by
  obtain ⟨q,hq,_,hD,hqm,hfixed⟩ := exists_fixed_prescribed_maximizer hd hA r hr hmax
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hR := roughExponentialBound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  let u := dualPotential A q hq
  have hu : Admissible u := dualPotential_admissible hd A q hq
  have humax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u :=
    (density_maximizer_dual hd hR hA0 q hq hqm).2
  have hs := maximizer_fourier_summable hd hR hA0 hu humax
  have he : smoothGibbsValue u =ᵐ[torusMeasure d] q.value :=
    (smoothGibbsValue_ae_eq u hs).trans (density_maximizer_gibbs hd hR hA0 q hq hqm).symm
  have hDist : IdentDistrib (smoothGibbsValue u) r.value (torusMeasure d) (torusMeasure d) :=
    (IdentDistrib.of_ae_eq (smoothGibbsValue_continuous u hs).aemeasurable he).trans hD
  have hinv : OriginPolarizationInvariant (smoothGibbsValue u) := by
    intro i a ha ha0
    exact (polarize_congr_ae i a he).trans ((hfixed i a ha ha0).trans he.symm)
  have hst := SteinerSelection.steiner_of_origin_invariant (smoothGibbsValue_continuous u hs) hinv
  have hvalue : functional A u = densityFunctional A r :=
    (density_maximizer_dual hd hR hA0 q hq hqm).1.trans
      (le_antisymm (hmax q hq) (hqm r hr))
  refine ⟨u,hu,hvalue,humax,hDist,(hDist.comp Real.continuous_mul_log.measurable).integral_eq,
    hst,SteinerSelection.steiner_of_normalized_exp (partition_pos hR hu) hst,?_⟩
  intro hn hh
  exact hn (hDist.ae_snd (measurableSet_singleton 1) hh)

#print axioms exists_fixed_prescribed_maximizer
#print axioms exists_equimeasurable_steiner_maximizer
end BecknerOnofri.PrescribedPolarization

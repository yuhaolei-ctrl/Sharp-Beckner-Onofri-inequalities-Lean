module

public import BecknerOnofri.SimultaneousOrbitCompact
public import BecknerOnofri.LipschitzSteinerSelection

@[expose] public section

/-! One compact simultaneous orbit produces two equimeasurable symmetric
limits. Independent one-function orbit choices are not substituted here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri CoordinatePolarization

theorem exists_pair_fixed_orbit_limit {d : ℕ} (f g : Torus d → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    ∃ p : (Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ),p∈closure (boundedPairOrbit f g) ∧
      LipschitzWith K p.1 ∧ LipschitzWith L p.2 ∧
      IdentDistrib p.1 f (torusMeasure d) (torusMeasure d) ∧
      IdentDistrib p.2 g (torusMeasure d) (torusMeasure d) ∧
      OriginPolarizationInvariant p.1 ∧ OriginPolarizationInvariant p.2 := by
  let fB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f,hf.continuous⟩
  let gB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨g,hg.continuous⟩
  let w : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨CosineMomentWeight.weight d,CosineMomentWeight.weight_continuous d⟩
  let M : ((Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ)) → ℝ := fun p =>
    (∫ x,p.1 x*w x ∂torusMeasure d)+(∫ x,p.2 x*w x ∂torusMeasure d)
  have hM : Continuous M :=
    ((boundedMoment_continuous w).comp continuous_fst).add
      ((boundedMoment_continuous w).comp continuous_snd)
  have hnonempty : (closure (boundedPairOrbit f g)).Nonempty :=
    ⟨(fB,gB),subset_closure (show (fB,gB)∈boundedPairOrbit f g from PairOrbit.refl)⟩
  obtain ⟨p,hp,hmax⟩ := (compact_pair_orbit_closure f g hf hg).exists_isMaxOn hnonempty hM.continuousOn
  have hparts := pair_closure_subset f g hp
  have hfix (i : Fin d) (a : ℝ) (ha : -(1/2 : ℝ)<a) (ha0 : a<0) :
      polarize i a p.1=ᵐ[torusMeasure d] p.1 ∧ polarize i a p.2=ᵐ[torusMeasure d] p.2 := by
    have hp1 : MemLp p.1 2 (torusMeasure d) :=
      p.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hp2 : MemLp p.2 2 (torusMeasure d) :=
      p.2.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hw := CosineMomentWeight.weight_memLp d
    have hs := CosineMomentWeight.weight_strict i ha ha0
    have hm : ∀ x∈halfTorus i a,CosineMomentWeight.weight d (reflection i a x)≤CosineMomentWeight.weight d x := by
      intro x hx
      by_cases he : reflection i a x=x
      · rw [he]
      · exact (hs x hx he).le
    have h1 := moment_polarize_le i a hp1 hw hm
    have h2 := moment_polarize_le i a hp2 hw hm
    have hu := hmax (pair_closure_polarize hf hg hp i a)
    change (∫ x,polarize i a p.1 x*CosineMomentWeight.weight d x ∂torusMeasure d)+
      (∫ x,polarize i a p.2 x*CosineMomentWeight.weight d x ∂torusMeasure d)≤
      (∫ x,p.1 x*CosineMomentWeight.weight d x ∂torusMeasure d)+
      (∫ x,p.2 x*CosineMomentWeight.weight d x ∂torusMeasure d) at hu
    exact ⟨polarize_ae_eq_of_moment_eq i a hp1 hw hs (by linarith),
      polarize_ae_eq_of_moment_eq i a hp2 hw hs (by linarith)⟩
  refine ⟨p,hp,closure_lipschitz hf hparts.1,closure_lipschitz hg hparts.2,?_,?_,
    fun i a ha ha0 => (hfix i a ha ha0).1,fun i a ha ha0 => (hfix i a ha ha0).2⟩
  · obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hp
    exact bounded_orbit_limit_identDistrib (fB.integrable _)
      (fun n => PairOrbit.left (hu n)) htu.fst_nhds
  · obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hp
    exact bounded_orbit_limit_identDistrib (gB.integrable _)
      (fun n => PairOrbit.right (hu n)) htu.snd_nhds

#print axioms exists_pair_fixed_orbit_limit
end BecknerOnofri.PolarizationL1

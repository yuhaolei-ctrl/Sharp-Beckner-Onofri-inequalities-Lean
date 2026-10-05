module

public import BecknerOnofri.PolarizationOrbitClosure

@[expose] public section

/-! Compactness of the actual simultaneous two-function polarization orbit. -/
noncomputable section
open Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization

inductive PairOrbit {d : ℕ} (f g : Torus d → ℝ) :
    (Torus d → ℝ) → (Torus d → ℝ) → Prop
  | refl : PairOrbit f g f g
  | step {u v : Torus d → ℝ} : PairOrbit f g u v → (i : Fin d) → (a : ℝ) →
      PairOrbit f g (polarize i a u) (polarize i a v)

theorem PairOrbit.left {d : ℕ} {f g u v : Torus d → ℝ}
    (h : PairOrbit f g u v) : Orbit f u := by
  induction h with
  | refl => exact Orbit.refl
  | step h i a ih => exact Orbit.step ih i a

theorem PairOrbit.right {d : ℕ} {f g u v : Torus d → ℝ}
    (h : PairOrbit f g u v) : Orbit g v := by
  induction h with
  | refl => exact Orbit.refl
  | step h i a ih => exact Orbit.step ih i a

def boundedPairOrbit {d : ℕ} (f g : Torus d → ℝ) :
    Set ((Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ)) := {p | PairOrbit f g p.1 p.2}

lemma pair_closure_subset {d : ℕ} (f g : Torus d → ℝ) :
    closure (boundedPairOrbit f g)⊆(closure (boundedOrbit f))×ˢ(closure (boundedOrbit g)) := by
  apply closure_minimal ?_ (isClosed_closure.prod isClosed_closure)
  intro p hp
  have h : PairOrbit f g p.1 p.2 := hp
  exact ⟨subset_closure h.left,subset_closure h.right⟩

theorem compact_pair_orbit_closure {d : ℕ} (f g : Torus d → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    IsCompact (closure (boundedPairOrbit f g)) := by
  let fB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f,hf.continuous⟩
  let gB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨g,hg.continuous⟩
  have hfC := compact_orbit_closure f hf (fun x => fB.norm_coe_le_norm x)
  have hgC := compact_orbit_closure g hg (fun x => gB.norm_coe_le_norm x)
  exact (hfC.prod hgC).of_isClosed_subset isClosed_closure (pair_closure_subset f g)

theorem pair_closure_polarize {d : ℕ} {f g : Torus d → ℝ} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    {p : (Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ)} (hp : p∈closure (boundedPairOrbit f g))
    (i : Fin d) (a : ℝ) :
    (boundedPolarize i a p.1 (closure_lipschitz hf (pair_closure_subset f g hp).1),
     boundedPolarize i a p.2 (closure_lipschitz hg (pair_closure_subset f g hp).2))∈
      closure (boundedPairOrbit f g) := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hp
  have ho (n : ℕ) : PairOrbit f g (u n).1 (u n).2 := hu n
  let v : ℕ → (Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ) := fun n =>
    (boundedPolarize i a (u n).1 ((ho n).left.lipschitz hf),
     boundedPolarize i a (u n).2 ((ho n).right.lipschitz hg))
  have hv (n : ℕ) : v n∈boundedPairOrbit f g := PairOrbit.step (ho n) i a
  apply mem_closure_of_tendsto (f := v) (b := atTop) ?_ (Filter.Eventually.of_forall hv)
  apply Filter.Tendsto.prodMk_nhds
  · apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact polarize_tendstoUniformly i a (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu.fst_nhds)
  · apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact polarize_tendstoUniformly i a (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu.snd_nhds)

#print axioms compact_pair_orbit_closure
#print axioms pair_closure_polarize
end BecknerOnofri.PolarizationL1

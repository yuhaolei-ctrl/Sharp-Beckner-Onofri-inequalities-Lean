import BecknerOnofri.CoordinateOrbitCompact

/-! A single-coordinate rearrangement retains symmetry and monotonicity
already obtained in every other coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open MeasureTheory Set Filter Legacy.TorusEndpoint
open scoped Topology BoundedContinuousFunction
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri.CoordinatePolarization

def SteinerAt {d : ℕ} (j : Fin d) (f : Torus d → ℝ) : Prop :=
  (∀ x, f (Function.update x j (-x j))=f x) ∧
  ∀ x, AntitoneOn (fun t : ℝ => f (Function.update x j (t : UnitAddCircle))) (Icc 0 (1/2))

lemma reflection_update_other {d : ℕ} {i j : Fin d} (hji : j≠i)
    (a : ℝ) (x : Torus d) (t : UnitAddCircle) :
    reflection i a (Function.update x j t)=Function.update (reflection i a x) j t := by
  funext k
  by_cases hk : k=j
  · subst k
    simp [reflection,hji]
  · by_cases hki : k=i
    · subst k
      simp [reflection,Ne.symm hji]
    · simp [reflection,hk,hki]

lemma polarize_update_other {d : ℕ} {i j : Fin d} (hji : j≠i)
    (a : ℝ) (f : Torus d → ℝ) (x : Torus d) (t : UnitAddCircle) :
    polarize i a f (Function.update x j t)=
      if x∈halfTorus i a then
        max (f (Function.update x j t)) (f (Function.update (reflection i a x) j t))
      else min (f (Function.update x j t)) (f (Function.update (reflection i a x) j t)) := by
  have hh : Function.update x j t∈halfTorus i a ↔ x∈halfTorus i a := by
    simp only [halfTorus,mem_setOf_eq,Function.update_of_ne (Ne.symm hji)]
  simp only [polarize,reflection_update_other hji]
  rw [hh]

lemma polarize_steinerAt {d : ℕ} {i j : Fin d} (hji : j≠i) (a : ℝ)
    {f : Torus d → ℝ} (hf : SteinerAt j f) : SteinerAt j (polarize i a f) := by
  constructor
  · intro x
    rw [polarize_update_other hji]
    have hj : reflection i a x j=x j := by simp [reflection,hji]
    rw [hf.1 x,← hj,hf.1 (reflection i a x)]
    rfl
  · intro x s hs t ht hst
    change polarize i a f (Function.update x j (t : UnitAddCircle)) ≤
      polarize i a f (Function.update x j (s : UnitAddCircle))
    rw [polarize_update_other hji,polarize_update_other hji]
    split
    · exact max_le_max (hf.2 x hs ht hst) (hf.2 (reflection i a x) hs ht hst)
    · exact min_le_min (hf.2 x hs ht hst) (hf.2 (reflection i a x) hs ht hst)

lemma Orbit.steinerAt {d : ℕ} {i j : Fin d} (hji : j≠i) {f g : Torus d → ℝ}
    (h : Orbit i f g) (hf : SteinerAt j f) : SteinerAt j g := by
  induction h with
  | refl => exact hf
  | step hg a ih => exact polarize_steinerAt hji a ih

lemma steinerAt_uniform_limit {d : ℕ} {j : Fin d} {u : ℕ → Torus d → ℝ}
    {g : Torus d → ℝ} (hu : ∀ n, SteinerAt j (u n)) (ht : TendstoUniformly u g atTop) :
    SteinerAt j g := by
  constructor
  · intro x
    have h := ht.tendsto_at (Function.update x j (-x j))
    simp_rw [fun n => (hu n).1 x] at h
    exact tendsto_nhds_unique h (ht.tendsto_at x)
  · intro x s hs t hte hst
    exact le_of_tendsto_of_tendsto
      (ht.tendsto_at (Function.update x j (t : UnitAddCircle)))
      (ht.tendsto_at (Function.update x j (s : UnitAddCircle)))
      (Eventually.of_forall (fun n => (hu n).2 x hs hte hst))

theorem closure_preserves_steinerAt {d : ℕ} {i j : Fin d} (hji : j≠i)
    {f : Torus d → ℝ} (hf : SteinerAt j f) {g : Torus d →ᵇ ℝ}
    (hg : g∈closure (boundedOrbit i f)) : SteinerAt j g := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
  exact steinerAt_uniform_limit (fun n => (hu n).steinerAt hji hf)
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu)

#print axioms closure_preserves_steinerAt
end BecknerOnofri.CoordinateRearrangement

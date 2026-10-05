module

public import BecknerOnofri.CoordinateOrbitCompact

@[expose] public section

noncomputable section
open Set Filter Legacy.TorusEndpoint
open scoped Topology BoundedContinuousFunction
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri.CoordinatePolarization

lemma Orbit.range_property {d : ℕ} {i : Fin d} {f g : Torus d → ℝ}
    (h : Orbit i f g) {P : ℝ → Prop} (hf : ∀ x, P (f x)) : ∀ x, P (g x) := by
  induction h with
  | refl => exact hf
  | step hg a ih =>
    intro x
    rcases polarize_value_or_reflected i a _ x with he | he <;> rw [he] <;> exact ih _

lemma closure_range_closed {d : ℕ} {i : Fin d} {f : Torus d → ℝ}
    {s : Set ℝ} (hs : IsClosed s) (hf : ∀ x, f x∈s) {g : Torus d →ᵇ ℝ}
    (hg : g∈closure (boundedOrbit i f)) : ∀ x, g x∈s := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
  intro x
  exact hs.mem_of_tendsto ((ContinuousEvalConst.continuous_eval_const x).tendsto g |>.comp htu)
    (Eventually.of_forall (fun n => (hu n).range_property hf x))

lemma closure_nonneg {d : ℕ} {i : Fin d} {f : Torus d → ℝ}
    (hf : ∀ x,0≤f x) {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit i f)) :
    ∀ x,0≤g x := closure_range_closed isClosed_Ici hf hg

#print axioms closure_nonneg
end BecknerOnofri.CoordinateRearrangement

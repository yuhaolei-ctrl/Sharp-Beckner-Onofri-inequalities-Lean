import BecknerOnofri.CoordinateRearrangementDefinitions
import BecknerOnofri.CoordinateCanonicalIdentification
import BecknerOnofri.CoordinateRearrangementOrder
import BecknerOnofri.CoordinateOrbitRange

/-! Finite successive canonical coordinate rearrangements. Previously
obtained coordinate monotonicity is retained at each step. -/
noncomputable section
open MeasureTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri
open HighDim.CoordinateRearrangementStatement

lemma steinerAt_of_fibers {d : ℕ} {i : Fin d} {f : Torus d → ℝ}
    (hf : ∀ x, SteinerSelection.Steiner (fiber i f x)) : SteinerAt i f := by
  constructor
  · intro x
    have h := (hf x).1 0 (fun _ => x i)
    simpa only [fiber,Function.update_self,Function.update_eq_self] using h
  · intro x s hs t ht hst
    have h := (hf x).2 (0 : Torus 1) 0 hs ht hst
    simpa only [fiber,SteinerFromPolarization.slice,Function.update_self] using h

/-- Any property preserved on single-coordinate orbit closures survives the
finite canonical construction. This interface is used with actual global
optimality, whose closure property has already been proved. -/
theorem exists_canonical_chain {d : ℕ} (is : List (Fin d)) {K : ℝ≥0}
    (P : (Torus d →ᵇ ℝ) → Prop)
    (hP : ∀ (i : Fin d) (f g : Torus d →ᵇ ℝ), LipschitzWith K f →
      g∈closure (boundedOrbit i f) → P f → P g)
    (f : Torus d →ᵇ ℝ) (hf : LipschitzWith K f) (hf0 : ∀ x,0≤f x) (hfP : P f) :
    ∃ g : Torus d →ᵇ ℝ, CanonicalChain is f g ∧ LipschitzWith K g ∧
      (∀ x,0≤g x) ∧ P g ∧ (∀ j∈is,SteinerAt j g) ∧
      (∀ j,SteinerAt j f → SteinerAt j g) := by
  induction is generalizing f with
  | nil =>
    exact ⟨f,.nil _,hf,hf0,hfP,by simp,fun _ h => h⟩
  | cons i is ih =>
    obtain ⟨h,hh,hhL,_,hhS,hhCanon⟩ := exists_canonical_coordinate_limit i f hf hf0
    have hh0 := closure_nonneg hf0 hh
    have hhP := hP i f h hf hh hfP
    obtain ⟨g,hgChain,hgL,hg0,hgP,hgS,hgKeep⟩ := ih h hhL hh0 hhP
    have hhi : SteinerAt i h := steinerAt_of_fibers hhS
    have hkeep (j : Fin d) (hj : SteinerAt j f) : SteinerAt j h := by
      by_cases hji : j=i
      · simpa only [hji] using hhi
      · exact closure_preserves_steinerAt hji hj hh
    refine ⟨g,.cons hhCanon hgChain,hgL,hg0,hgP,?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hgKeep _ hhi
      · exact hgS j hj
    · intro j hj
      exact hgKeep j (hkeep j hj)

#print axioms exists_canonical_chain
end BecknerOnofri.CoordinateRearrangement

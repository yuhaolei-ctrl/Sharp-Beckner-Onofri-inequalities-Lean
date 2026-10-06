module

public import BecknerOnofri.LocalElevenCore.ActiveFactorNonzero

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ReducedEquation

/-- The source proof's divisibility argument: every two active squared amplitudes
of a sufficiently small genuine reduced critical point are equal. -/
theorem equal_active_squares {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : Input d in 𝓝 (1,0),reduced hd (realEmbedding d x)=0 →
      ∀ i j : Fin d,x.2 i≠0 → x.2 j≠0 → x.2 i^2=x.2 j^2 := by
  have hpair (i j : Fin d) : ∀ᶠ x : Input d in 𝓝 (1,0),
      reduced hd (realEmbedding d x)=0 → x.2 i≠0 → x.2 j≠0 → x.2 i^2=x.2 j^2 := by
    by_cases hij : i=j
    · subst j
      exact Filter.Eventually.of_forall (fun _ _ _ _ => rfl)
    obtain ⟨H,_,_,hH⟩ := exists_nonzero_squared_difference_factor hd i j hij
    filter_upwards [hH,reduced_zero_iff_coordinate_factors hd] with x hH hfactor
    intro hx hi hj
    have hfi := ((hfactor.mp hx) i).resolve_left hi
    have hfj := ((hfactor.mp hx) j).resolve_left hj
    have he := hH.2
    rw [hfi,hfj,sub_self] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hH.1.ne')
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hpair i))]
    with x hx
  intro hz i j
  exact hx i j hz

#print axioms equal_active_squares
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor

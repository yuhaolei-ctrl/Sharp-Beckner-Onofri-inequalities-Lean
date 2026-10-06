module

public import BecknerOnofri.LocalElevenCore.SubsetUniqueness
public import BecknerOnofri.LocalElevenCore.EqualActiveFourier

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry ReducedEquation

theorem equal_squares_supported_line {d : ℕ} (z : Coordinates d) (hz : z≠0)
    (he : ∀ i j : Fin d,z i≠0 → z j≠0 → ‖z i‖^2=‖z j‖^2) :
    ∃ I : Finset (Fin d), ∃ j : Fin d, ∃ hj : j∈I,
      0<‖z j‖ ∧ (fun i => (‖z i‖:ℂ))=SubsetDiagonal.line I ‖z j‖ := by
  classical
  obtain ⟨j,hj⟩ : ∃ j,z j≠0 := by
    by_contra hn
    apply hz
    funext j
    by_contra hj
    exact hn ⟨j,hj⟩
  let I : Finset (Fin d) := Finset.univ.filter (fun i => z i≠0)
  have hmem : j∈I := by simp [I,hj]
  refine ⟨I,j,hmem,norm_pos_iff.mpr hj,?_⟩
  funext i
  by_cases hi : z i=0
  · simp [I,hi]
  · have hs := he i j hi hj
    have hn : ‖z i‖=‖z j‖ := by nlinarith [norm_nonneg (z i),norm_nonneg (z j)]
    simp [I,hi,hn]

theorem all_supported_parameter_unique {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),∀ I : Finset (Fin d),∀ j : Fin d,
      ∀ hj : j∈I,‖x.2 j‖≠0 → reduced hd (x.1,SubsetDiagonal.line I ‖x.2 j‖)=0 →
        SubsetDiagonal.parameter hd I j hj ‖x.2 j‖=x.1 := by
  have h (I : Finset (Fin d)) (j : Fin d) :
      ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),∀ hj : j∈I,‖x.2 j‖≠0 →
        reduced hd (x.1,SubsetDiagonal.line I ‖x.2 j‖)=0 →
          SubsetDiagonal.parameter hd I j hj ‖x.2 j‖=x.1 := by
    by_cases hj : j∈I
    · have ht : Tendsto (fun x : ℝ × Coordinates d => (x.1,‖x.2 j‖))
          (𝓝 (1,0)) (𝓝 (1,0)) := by
        have hc : Continuous (fun x : ℝ × Coordinates d => (x.1,‖x.2 j‖)) :=
          continuous_fst.prodMk (((continuous_apply j).comp continuous_snd).norm)
        simpa only [Pi.zero_apply,norm_zero] using hc.tendsto (1,0)
      filter_upwards [ht.eventually (SubsetDiagonal.supported_parameter_unique hd I j hj),
        ht.eventually ((SubsetDiagonal.embedding_tendsto I).eventually (graph_full_iff_reduced hd))]
        with x hu hf
      intro hj' hn hr
      exact (hu hn).mp (hf.mpr hr)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hj h))
  exact Filter.eventually_all.mpr (fun I => Filter.eventually_all.mpr (h I))

#print axioms all_supported_parameter_unique
end BecknerOnofri.HighDim.LocalEleven

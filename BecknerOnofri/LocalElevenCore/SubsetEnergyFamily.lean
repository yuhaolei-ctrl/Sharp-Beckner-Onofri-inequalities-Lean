import BecknerOnofri.LocalElevenCore.SubsetBranchFromAmplitude
import BecknerOnofri.LocalElevenCore.SubsetUniqueness

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open SubsetDiagonal LocalReductionStatement

/-- One analytic squared-amplitude function for every support of size n,
with the actual PDE and physical pressure assertions on the same branch. -/
theorem supported_energy_family {d n : ℕ} (hd : 11≤d) (hn : 0<n) (hnd : n≤d) :
    SupportedEnergyFamily d n := by
  obtain ⟨J,hJsub,hJcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin d))) (by simpa using hnd)
  have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j,hj⟩ := hJ
  let D := pitchforkData hd J j hj
  obtain ⟨r,hr,hr0,hrd,he,hp⟩ := AnalyticPitchfork.exists_positive_squared_amplitude D
    (coefficient_pos hd J ⟨j,hj⟩)
  have hc : D.coefficient=supportCoefficient d n := by
    simp only [D,pitchforkData,coefficient,supportCoefficient,hJcard]
  refine ⟨r,hr,hr0,?_,?_,?_⟩
  · simpa only [hc] using hrd
  · simpa only [hc] using he
  · intro I hIcard
    have hI : I.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i,hi⟩ := hI
    have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := hr.continuousAt.sqrt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa only [hr0,Real.sqrt_zero] using h
    have heI : (fun δ => r δ-δ/coefficient I) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2) := by
      simpa only [D,pitchforkData,coefficient,hJcard,hIcard] using he
    have hpI : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧
        parameter hd I i hi (Real.sqrt (r δ))=1/(1-δ) := by
      filter_upwards [hp,ht.eventually (parameter_eq_of_card_eq hd J I j i hj hi
        (hJcard.trans hIcard.symm))] with δ hp heq
      exact ⟨hp.1,heq.symm.trans hp.2⟩
    obtain ⟨U,hu,henergy⟩ := supported_branch_of_parameter hd I i hi hr hr0 heI hpI
    exact ⟨U,hu,by simpa only [hIcard] using henergy⟩

#print axioms supported_energy_family
end BecknerOnofri.HighDim.LocalEleven

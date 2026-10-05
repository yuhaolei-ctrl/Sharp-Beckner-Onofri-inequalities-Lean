import BecknerOnofri.LocalElevenCore.SupportedDeltaIdentification
import BecknerOnofri.LocalElevenCore.SupportedExhaustiveness

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open ContinuousGibbs ContinuousFirstShell ReducedEquation
open BecknerOnofri.HighDim.ContinuousSymmetry (translation)

theorem all_scalar_identifications {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1,0),∀ I : Finset (Fin d),∀ j : Fin d,∀ hj : j∈I,
      0<‖fourierCoeff x.2 (axisFrequency j)‖ →
      let t := ‖fourierCoeff x.2 (axisFrequency j)‖
      0<1-1/SubsetDiagonal.parameter hd I j hj t ∧
        branch hd I (1-1/SubsetDiagonal.parameter hd I j hj t)=
          SubsetDiagonal.branchPotential hd I j hj t := by
  have h (I : Finset (Fin d)) (j : Fin d) :
      ∀ᶠ x : ℝ × Space d in 𝓝 (1,0),∀ hj : j∈I,
        0<‖fourierCoeff x.2 (axisFrequency j)‖ →
        let t := ‖fourierCoeff x.2 (axisFrequency j)‖
        0<1-1/SubsetDiagonal.parameter hd I j hj t ∧
          branch hd I (1-1/SubsetDiagonal.parameter hd I j hj t)=
            SubsetDiagonal.branchPotential hd I j hj t := by
    by_cases hj : j∈I
    · have ht : Tendsto (fun x : ℝ × Space d => ‖fourierCoeff x.2 (axisFrequency j)‖)
          (𝓝 (1,0)) (𝓝 0) := by
        have hc : Continuous (fun x : ℝ × Space d => ‖coordinates d x.2 j‖) :=
          (((continuous_apply j).comp (coordinates d).continuous).comp continuous_snd).norm
        have hh := hc.tendsto (1,0)
        simpa only [map_zero,Pi.zero_apply,norm_zero,coordinates_apply,coefficient_eq_fourierCoeff]
          using hh
      filter_upwards [ht.eventually (scalar_branch_identification hd I j hj)] with x hx
      intro hj'
      exact hx
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hj h))
  exact Filter.eventually_all.mpr (fun I => Filter.eventually_all.mpr (h I))

/-- The common delta-parameter family exhausts every small nonzero full Euler solution. -/
theorem small_solution_branch {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1,0),MeanZero x.2 → full d x.1 x.2=0 → x.2≠0 →
      0<1-1/x.1 ∧ ∃ I : Finset (Fin d),I.Nonempty ∧ ∃ a : Torus d,
        x.2=translation a (branch hd I (1-1/x.1)) := by
  filter_upwards [small_solution_supported hd,all_scalar_identifications hd] with x hx hi
  intro hm hf hn
  obtain ⟨I,j,hj,t,a,ht,hcoeff,hparam,hu⟩ := hx hm hf hn
  have hs := hi I j hj (hcoeff ▸ ht)
  dsimp only at hs
  rw [← hcoeff] at hs
  rw [← hparam] at hs
  exact ⟨hs.1,I,⟨j,hj⟩,a,hu.trans (congrArg (translation a) hs.2.symm)⟩

#print axioms small_solution_branch
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily

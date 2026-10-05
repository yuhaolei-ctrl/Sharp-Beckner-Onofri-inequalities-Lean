import BecknerOnofri.SupportedBranchStatementDefinitions
import BecknerOnofri.LocalElevenCore.SubsetPositiveBranch

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven

theorem supported_stationary_branch {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (hI : I.Nonempty) : LocalReductionStatement.SupportedStationaryBranch d I := by
  obtain ⟨r,U,ha,h0,hdiff,herr,hlim,hprop⟩ := SubsetDiagonal.exists_supported_branch hd I hI
  refine ⟨r,U,ha,h0,hdiff,herr,hlim,?_⟩
  filter_upwards [hprop] with δ h
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,?_⟩
  intro j
  rw [h.2.2.2.2.2.2.1 j]
  have hn : (Real.sqrt (r δ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr h.1).ne'
  by_cases hj : j∈I <;> simp [hj,hn]

#print axioms supported_stationary_branch
end BecknerOnofri.HighDim.LocalEleven

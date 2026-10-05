module

public import BecknerOnofri.SupportedClassificationStatementDefinitions
public import BecknerOnofri.LocalElevenCore.SupportedDeltaExhaustiveness

@[expose] public section

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open SupportedFamily

theorem supported_classification {d : ℕ} (hd : 11≤d) :
    LocalReductionStatement.SupportedClassification d := by
  refine ⟨amplitude hd,branch hd,?_,branch_profile hd,?_⟩
  · intro n hn hnd
    have h := amplitude_spec hd hn hnd
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  · filter_upwards [small_solution_branch hd] with x hx
    intro hm hf hn
    exact hx hm ((ReducedEquation.full_zero_iff_stationary (by omega) _ _).mpr ⟨hm,hf⟩) hn

#print axioms supported_classification
end BecknerOnofri.HighDim.LocalEleven

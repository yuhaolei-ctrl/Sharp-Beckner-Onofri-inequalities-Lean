module

public import BecknerOnofri.StableSupportedClassificationDefinitions
public import BecknerOnofri.LocalElevenCore.SupportedClassification
public import BecknerOnofri.LocalElevenCore.SupportedRawClassification
public import BecknerOnofri.LocalElevenCore.SupportedFamilyStability
public import BecknerOnofri.LocalElevenCore.SupportedFamilyEnergyOrdering

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open SupportedFamily ContinuousGibbs

theorem stable_supported_classification {d : ℕ} (hd : 11≤d) :
    LocalReductionStatement.StableSupportedClassification d := by
  refine ⟨amplitude hd,branch hd,?_,branch_profile hd,?_,raw_sobolev_classification hd,?_⟩
  · intro n hn hnd
    have h := amplitude_spec hd hn hnd
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  · filter_upwards [small_solution_branch hd] with x hx
    intro hm hf hn
    exact hx hm ((ReducedEquation.full_zero_iff_stationary (by omega) _ _).mpr ⟨hm,hf⟩) hn
  · have hs : ∀ᶠ δ in 𝓝[>] (0:ℝ),∀ I : Finset (Fin d),I.Nonempty → I.card<d →
        ∃ v q : Space d,InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
          0<secondVariation ((1/(1-δ))*spectralThreshold d) (branch hd I δ) v ∧
          secondVariation ((1/(1-δ))*spectralThreshold d) (branch hd I δ) q<0 := by
      apply eventually_all.mpr
      intro I
      by_cases hi : I.Nonempty
      · by_cases hc : I.card<d
        · exact (proper_branch_saddle hd I hi hc).mono (fun δ h _ _ => h)
        · exact Eventually.of_forall (fun δ _ h => (hc h).elim)
      · exact Eventually.of_forall (fun δ h => (hi h).elim)
    have he : ∀ᶠ δ in 𝓝[>] (0:ℝ),∀ I J : Finset (Fin d),I.Nonempty → I.card<J.card →
        dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd I δ)<
          dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd J δ) := by
      apply eventually_all.mpr
      intro I
      apply eventually_all.mpr
      intro J
      by_cases hi : I.Nonempty
      · by_cases hc : I.card<J.card
        · exact (branch_energy_ordering_ereal hd I J hi hc).mono (fun δ h _ _ => h)
        · exact Eventually.of_forall (fun δ _ h => (hc h).elim)
      · exact Eventually.of_forall (fun δ h => (hi h).elim)
    filter_upwards [full_branch_morse_bott hd,hs,he] with δ hm hs he
    exact ⟨hm,hs,he⟩

#print axioms stable_supported_classification
end BecknerOnofri.HighDim.LocalEleven

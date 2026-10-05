import BecknerOnofri.LocalElevenCore.SubsetEnergyFamily
import BecknerOnofri.QuadraticEnergyComparison

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open LocalReductionStatement

/-- Actual stationary branches on two different support sizes can be chosen with
the strict energy ordering from the paper, not merely ordering of quartic coefficients. -/
theorem exists_ordered_supported_branches {d : ℕ} (hd : 11≤d)
    (I J : Finset (Fin d)) (hI : I.Nonempty) (hIJ : I.card<J.card) :
    ∃ rI rJ : ℝ → ℝ, ∃ UI UJ : ℝ → ContinuousGibbs.Space d,
      SupportedProfile d I rI UI ∧ SupportedProfile d J rJ UJ ∧
      ∀ᶠ δ in 𝓝[>] (0:ℝ),
        (dualFunctional ((1/(1-δ))*spectralThreshold d) (UI δ)).toReal <
          (dualFunctional ((1/(1-δ))*spectralThreshold d) (UJ δ)).toReal := by
  have hi : 0<I.card := Finset.card_pos.mpr hI
  have hj : 0<J.card := hi.trans hIJ
  have hiD : I.card≤d := by simpa using Finset.card_le_card (Finset.subset_univ I)
  have hjD : J.card≤d := by simpa using Finset.card_le_card (Finset.subset_univ J)
  obtain ⟨rI,_,_,_,_,hri⟩ := supported_energy_family hd hi hiD
  obtain ⟨rJ,_,_,_,_,hrj⟩ := supported_energy_family hd hj hjD
  obtain ⟨UI,hUI,hEi⟩ := hri I rfl
  obtain ⟨UJ,hUJ,hEj⟩ := hrj J rfl
  exact ⟨rI,rJ,UI,UJ,hUI,hUJ,quadratic_energy_compare
    (LocalQuartic.branch_pressure_strictMono hd hi hIJ hjD) hEi hEj⟩

#print axioms exists_ordered_supported_branches
end BecknerOnofri.HighDim.LocalEleven

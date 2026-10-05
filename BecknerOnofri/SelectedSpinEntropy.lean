import BecknerOnofri.SpinEntropyChain
import BecknerOnofri.SelectedSpinChannel

/-! The completed discrete entropy comparison for the actual selected Gibbs
density and its thirteen-state count law. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BecknerOnofri.HighDim.Spin

theorem count_entropy_le_conditional (ρ : ProbabilityDensity 12)
    (hρ : EntropyShearer.PositiveBounded ρ.value) (hsym : Exchangeable (channelLaw ρ)) :
    relativeEntropy (countLaw (channelLaw ρ)) reference ≤
      ∑ i : Fin 12, ∫ x, ρ.value x * binaryCost
        (ConditionalEntropy.conditionalCosineMoment ρ.value i 1 x) ∂torusMeasure 12 := by
  rw [← exchangeable_entropy hsym]
  exact channel_entropy_le_conditional ρ hρ

end BecknerOnofri.HighDim.Spin

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SmoothFourier

theorem spinDensity_positiveBounded {u : TorusL2 12} (hu : Selected u) :
    EntropyShearer.PositiveBounded (spinDensity hu).value :=
  EntropyShearer.positiveBounded_of_continuous_pos
    (smoothGibbsValue_continuous u (fourier_norm_summable hu))
    (smoothGibbsValue_pos rough hu.1)

theorem selected_spin_entropy {u : TorusL2 12} (hu : Selected u) :
    Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference ≤
      ∑ i : Fin 12, ∫ x, (spinDensity hu).value x * Spin.binaryCost
        (ConditionalEntropy.conditionalCosineMoment (spinDensity hu).value i 1 x)
          ∂torusMeasure 12 :=
  Spin.count_entropy_le_conditional (spinDensity hu) (spinDensity_positiveBounded hu)
    (selected_spin_exchangeable hu)

#print axioms selected_spin_entropy
end BecknerOnofri.HighDim.SelectedNumericalModel

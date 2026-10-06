module

public import BecknerOnofri.SpinChannelSymmetry
public import BecknerOnofri.SpinChannelMean
public import BecknerOnofri.SpinMixtureFeasibility
public import BecknerOnofri.SelectedCubicSymmetry
public import BecknerOnofri.EndpointDuality

@[expose] public section

/-! Application of the new entropy route to the actual selected maximizer.
Neither permutation symmetry nor the cosine mixture is an added hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SmoothFourier
open ContinuousGibbs ContinuousSymmetry

def spinDensity {u : TorusL2 12} (hu : Selected u) : HighDim.ProbabilityDensity 12 :=
  Bridge.rawDensity (smoothGibbsDensity rough hu.1 (fourier_norm_summable hu))

theorem spinDensity_mixture {u : TorusL2 12} (hu : Selected u) :
    GenericCosineRepresentation.HasPositiveCosineMixture (spinDensity hu).value :=
  GenericCosineRepresentation.steiner_maximizer_mixture (by norm_num)
    (by norm_num : (0:ℝ)<1/2) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2

theorem spinDensity_symmetric {u : TorusL2 12} (hu : Selected u)
    (π : Equiv.Perm (Fin 12)) (x : HighDim.Torus 12) :
    (spinDensity hu).value (pointPermutation π x)=(spinDensity hu).value x := by
  change smoothGibbsValue u (pointPermutation π x)=smoothGibbsValue u x
  rw [← potential_normalized hu,← potential_normalized hu]
  change permutation π (normalized (potential u)) x=normalized (potential u) x
  rw [← normalized_permutation,CosineCoefficientLattice.selected_permutation_potential hu]

theorem selected_spin_exchangeable {u : TorusL2 12} (hu : Selected u) :
    Spin.Exchangeable (Spin.channelLaw (spinDensity hu)) :=
  Spin.channelLaw_exchangeable (spinDensity hu) (spinDensity_symmetric hu)

theorem selected_spin_feasible {u : TorusL2 12} (hu : Selected u) :
    Spin.Feasible (Spin.countLaw (Spin.channelLaw (spinDensity hu))) :=
  Spin.channel_count_feasible (spinDensity hu) (spinDensity_mixture hu)

end BecknerOnofri.HighDim.SelectedNumericalModel

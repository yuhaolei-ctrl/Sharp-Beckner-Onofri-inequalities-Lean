module

public import BecknerOnofri.ElevenFourierDecay
public import BecknerOnofri.ElevenPeriodizedContinuity
public import BecknerOnofri.GraphRegularity

@[expose] public section

/-! Smoothness of the actual periodized profile follows from its exponential
Fourier decay and pointwise continuity, without changing representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.Eleven

lemma periodizedProfile_smooth : SmoothOnTorus periodizedProfile := by
  let u : ContinuousGibbs.Space 11 := ⟨periodizedProfile, periodizedProfile_continuous⟩
  apply GraphRegularity.smooth_of_radial u
  intro m
  unfold GraphRegularity.Radial
  apply (periodized_fourier_radial m).congr
  intro k
  dsimp only
  rw [ContinuousFirstShell.coefficient_eq_fourierCoeff]
  rfl

theorem profile_regular :
    ∃ ρ : ProbabilityDensity 11, ρ.value = periodizedProfile ∧
      ρ.FiniteEntropy ∧ SmoothOnTorus ρ.value ∧ ∀ x, 0 < ρ.value x :=
  ⟨competitorDensity, rfl, competitorDensity_finiteEntropy,
    periodizedProfile_smooth, periodizedProfile_pos⟩

#print axioms profile_regular
end BecknerOnofri.HighDim.Eleven

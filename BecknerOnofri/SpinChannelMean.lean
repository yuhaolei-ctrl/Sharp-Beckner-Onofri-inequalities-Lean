module

public import BecknerOnofri.SpinCountMoments

@[expose] public section

/-! The mean coordinate of the compressed distribution is exactly the first
cosine moment of the actual symmetric density. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem moment_zero_eq_meanCoordinate (j : Count) : moment 0 j=meanCoordinate j := by
  have he : ∀ j : Count,momentQ 0 j=meanCoordinateQ j := by decide +kernel
  exact congrArg (fun x : ℚ => (x:ℝ)) (he j)

theorem firstCoordinates_zero : firstCoordinates 0={(0:Fin 12)} := by decide +kernel

theorem channel_count_mean (ρ : ProbabilityDensity 12) (hρ : Exchangeable (channelLaw ρ)) :
    mean (countLaw (channelLaw ρ))=
      ∫ x,ρ.value x*(fourier 1 (x (0:Fin 12))).re ∂torusMeasure 12 := by
  have he := exchangeable_joint_moment hρ 0
  simp_rw [moment_zero_eq_meanCoordinate] at he
  change _ = mean (countLaw (channelLaw ρ)) at he
  rw [← he,channelLaw_joint_moment,firstCoordinates_zero]
  simp

#print axioms channel_count_mean
end BecknerOnofri.HighDim.Spin

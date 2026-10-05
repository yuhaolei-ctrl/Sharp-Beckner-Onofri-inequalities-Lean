module

public import BecknerOnofri.SpinChannelMean
public import BecknerOnofri.SpinMixtureFeasibility
public import BecknerOnofri.SpinSmallMean
public import BecknerOnofri.CircleSmallGamma

@[expose] public section

/-! The small-mean finite-spin/scalar conclusion for the actual channel of
a positive cosine mixture, with its mean supplied by the genuine integral. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.Spin

theorem small_mean_gamma (t : ℝ) (q : Count → ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hq : FeasibleAt t q) :
    t^4/50≤functional q+12*CircleScalar.gamma t := by
  have hs := small_mean_spin_inequality t q ht ht1 hq
  have hg := CircleScalar.gamma_small_quartic_lower ht ht1
  linarith

theorem channel_small_mean_gamma (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value)
    (he : Exchangeable (channelLaw ρ)) (t : ℝ)
    (hm : (∫ x,ρ.value x*(fourier 1 (x (0:Fin 12))).re ∂torusMeasure 12)=t)
    (ht : 0≤t) (ht1 : t≤1/16) :
    t^4/50≤functional (countLaw (channelLaw ρ))+12*CircleScalar.gamma t := by
  apply small_mean_gamma t _ ht ht1
  exact ⟨channel_count_feasible ρ hρ,(channel_count_mean ρ he).trans hm⟩

#print axioms channel_small_mean_gamma
end BecknerOnofri.HighDim.Spin

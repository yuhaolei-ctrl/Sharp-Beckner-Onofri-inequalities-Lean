module

public import BecknerOnofri.CircleGammaDefinitions
public import BecknerOnofri.CircleRateLower
public import BecknerOnofri.CircleSmallMeanWeighted

@[expose] public section

/-! The complete small-mean γ bound, with the actual inverse Bessel mean,
actual rate function, actual weights and actual constrained minimum. -/
noncomputable section
open Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem besselMoment_one_eighth_lower : (1/16:ℝ)≤besselMoment 1 (1/8) := by
  have hn : (1/8:ℝ)≤bessel 1 (1/8) := by
    rw [bessel_series_eq]
    have hs := (besselOrderTerm_summable (1/8) 1).le_tsum 0
      (fun j _ => by unfold besselOrderTerm; positivity)
    simpa [besselOrderTerm] using hs
  have hd : bessel 0 (1/8)≤(2:ℝ) := by
    rw [bessel_zero_eq,besselI0Two_eq_series]
    have hs := besselSeries_upper (s:=(1/8:ℝ)^2) (by norm_num) (by norm_num)
    norm_num at hs ⊢
    linarith
  have hp : 0<bessel 0 (1/8) := by rw [bessel_zero_eq]; exact besselI0Two_pos _
  unfold besselMoment
  apply (le_div_iff₀ hp).mpr
  linarith

theorem parameter_small_mean {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) :
    besselMoment 1 (parameter t)=t ∧ 0≤parameter t ∧ parameter t≤1/8 := by
  have hc : Continuous (besselMoment 1) := continuous_iff_continuousAt.mpr
    (fun h => (besselMoment_first_derivative h).continuousAt)
  have hi := intermediate_value_Icc (by norm_num : (0:ℝ)≤1/8) hc.continuousOn
    (show t ∈ Icc (besselMoment 1 0) (besselMoment 1 (1/8)) from
      ⟨by simpa [besselMoment_one_zero] using ht,ht1.trans besselMoment_one_eighth_lower⟩)
  obtain ⟨h,hh,he⟩ := hi
  have hp : besselMoment 1 (parameter t)=t := Function.invFun_eq ⟨h,he⟩
  have heq : parameter t=h := besselMoment_first_strictMono.injective (hp.trans he.symm)
  exact ⟨hp,heq ▸ hh.1,heq ▸ hh.2⟩

theorem rate_small_quartic_lower {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) :
    t^2+t^4/4≤rate t := by
  obtain ⟨hm,hp,_⟩ := parameter_small_mean ht ht1
  have hl := rateAt_quartic_lower (parameter t) hp
  simpa [rateAt,rate,hm] using hl

theorem gamma_small_quartic_lower {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) :
    (3/40:ℝ)*t^4≤gamma t := by
  exact small_mean_weighted_candidate_lower t (rate t)
    (besselMoment 2 (parameter t)) (besselMoment 3 (parameter t)) ht ht1
    (rate_small_quartic_lower ht ht1)

#print axioms parameter_small_mean
#print axioms gamma_small_quartic_lower
end BecknerOnofri.HighDim.CircleScalar

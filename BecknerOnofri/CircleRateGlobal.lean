import BecknerOnofri.CircleBesselInverse
import BecknerOnofri.CircleRateLower

/-! Rate-function bounds on the entire mean interval, using the actual
inverse Bessel mean. The second bound is the input to the source's final
J-monotonicity argument near t=1. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem rate_quartic_lower {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    t^2+t^4/4≤rate t := by
  obtain ⟨hm,hp⟩ := parameter_mean ht ht1
  have hl := rateAt_quartic_lower (parameter t) hp
  simpa [rateAt,rate,hm] using hl

theorem parameter_lower {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    t/(2*(1-t^2))≤parameter t := by
  obtain ⟨hm,hp⟩ := parameter_mean ht ht1
  have hd := (besselMoment_first_derivative (parameter t)).deriv
  have hpos := besselMoment_first_deriv_pos (parameter t)
  rw [hd,hm] at hpos
  have he := besselMoment_recurrence (parameter t)
  rw [hm] at he
  have hc := mul_nonneg hp hpos.le
  apply (div_le_iff₀ (by nlinarith : 0<2*(1-t^2))).mpr
  nlinarith

theorem parameter_strictMono : StrictMonoOn parameter (Set.Ico 0 1) := by
  intro a ha b hb hab
  apply besselMoment_first_strictMono.lt_iff_lt.mp
  rw [(parameter_mean ha.1 ha.2).1,(parameter_mean hb.1 hb.2).1]
  exact hab

#print axioms rate_quartic_lower
#print axioms parameter_lower
end BecknerOnofri.HighDim.CircleScalar

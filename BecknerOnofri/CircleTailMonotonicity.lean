import BecknerOnofri.CircleTailDefinitions
import BecknerOnofri.CircleTailLogBound
import BecknerOnofri.CircleRateGlobal
import BecknerOnofri.SpinBinaryCost

/-! Analytic monotonicity of the source's final scalar lower bound J on
[0.999,1), proved along the genuine inverse Bessel parametrization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem tailBase_mono : MonotoneOn tailBase (Ico (999/1000) 1) := by
  intro a ha b hb hab
  have ha0 : 0≤a := by linarith [ha.1]
  have hb0 : 0≤b := by linarith [hb.1]
  obtain ⟨hRa,hpa⟩ := parameter_mean ha0 ha.2
  obtain ⟨hRb,hpb⟩ := parameter_mean hb0 hb.2
  have hpab : parameter a≤parameter b := by
    apply besselMoment_first_strictMono.le_iff_le.mp
    rw [hRa,hRb]
    exact hab
  let f : ℝ → ℝ := fun h => (13/40)*rateAt h+(27/40)*(besselMoment 1 h)^2-
    2*Spin.binaryCost (besselMoment 1 h)
  let f' : ℝ → ℝ := fun h => deriv (besselMoment 1) h*
    ((13/20)*h+(27/20)*besselMoment 1 h-
      Real.log (1+besselMoment 1 h)+Real.log (1-besselMoment 1 h))
  have hd (h : ℝ) (hlo : -1<besselMoment 1 h) (hhi : besselMoment 1 h<1) :
      HasDerivAt f (f' h) h := by
    have hm := (besselMoment_first_derivative h).differentiableAt.hasDerivAt
    have hi : HasDerivAt rateAt (2*h*deriv (besselMoment 1) h) h := by
      have he := (((hasDerivAt_id h).const_mul 2).mul hm).sub (log_bessel_derivative h)
      convert he using 1 <;> try rfl
      simp only [id_eq]
      ring
    have he := ((hi.const_mul (13/40)).add ((hm.pow 2).const_mul (27/40))).sub
      (((Spin.binaryCost_derivative (besselMoment 1 h) hlo hhi).comp h hm).const_mul 2)
    convert he using 1 <;> try rfl
    dsimp [f',Spin.binaryCostSlope]
    ring
  have hbounds (h : ℝ) (hh : h ∈ Icc (parameter a) (parameter b)) :
      (999/1000:ℝ)≤besselMoment 1 h ∧ besselMoment 1 h<1 := by
    have hlo := besselMoment_first_strictMono.monotone hh.1
    have hhi := besselMoment_first_strictMono.monotone hh.2
    rw [hRa] at hlo
    rw [hRb] at hhi
    exact ⟨ha.1.trans hlo,hhi.trans_lt hb.2⟩
  have hf' (h : ℝ) (hh : h ∈ Icc (parameter a) (parameter b)) : 0≤f' h := by
    obtain ⟨hlo,hhi⟩ := hbounds h hh
    have hR0 : 0≤besselMoment 1 h := by linarith
    have hinv : parameter (besselMoment 1 h)=h :=
      Function.leftInverse_invFun besselMoment_first_strictMono.injective h
    have hp := parameter_lower hR0 hhi
    rw [hinv] at hp
    have hc := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤13/20)
    have he : (13/20:ℝ)*(besselMoment 1 h/(2*(1-(besselMoment 1 h)^2)))=
        (13/40)*besselMoment 1 h/(1-(besselMoment 1 h)^2) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he] at hc
    have hl := tail_log_comparison (besselMoment 1 h) hlo hhi
    rw [Real.log_div (by linarith : 1+besselMoment 1 h≠0)
      (by linarith : 1-besselMoment 1 h≠0)] at hl
    exact mul_nonneg (besselMoment_first_deriv_pos h).le (by linarith)
  have hmono : MonotoneOn f (Icc (parameter a) (parameter b)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · intro h hh
      exact (hd h (by linarith [(hbounds h hh).1]) (hbounds h hh).2).continuousAt.continuousWithinAt
    · intro h hh
      have hmem := interior_subset hh
      exact (hd h (by linarith [(hbounds h hmem).1]) (hbounds h hmem).2).hasDerivWithinAt
    · intro h hh
      exact hf' h (interior_subset hh)
  have h := hmono ⟨le_rfl,hpab⟩ ⟨hpab,le_rfl⟩ hpab
  simpa [f,rateAt,tailBase,rate,hRa,hRb] using h

#print axioms tailBase_mono
end BecknerOnofri.HighDim.CircleScalar

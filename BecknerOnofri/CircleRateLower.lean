import BecknerOnofri.CircleRateDefinitions
import BecknerOnofri.CircleBesselComparison

/-! The source's quartic lower bound for the von Mises rate, parametrized
by its actual Bessel mean. This uses the proved Riccati comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar
open ContinuousGibbs GibbsTrialLower GinibreCovariance

theorem log_bessel_derivative (h : ℝ) :
    HasDerivAt (fun a : ℝ => Real.log (bessel 0 a)) (2*besselMoment 1 h) h := by
  let w := (2:ℝ) • cosine (circleFrequency 1)
  have hd := (hasFDerivAt_logPartitionReal (h • w)).comp_hasDerivAt h
    ((hasDerivAt_id h).smul_const w)
  change HasDerivAt (fun a : ℝ => logPartitionReal (a • w))
    (weightedMean (h • w) (1 • w)) h at hd
  simp only [one_smul,w,← trial_one_line,trial_logPartition,Nat.cast_one,one_mul,
    map_smul,smul_eq_mul,trial_one_mean,Int.natAbs_one] at hd
  simpa only [bessel_zero_eq,besselMoment_eq] using hd

theorem besselMoment_first_deriv_pos (h : ℝ) : 0<deriv (besselMoment 1) h := by
  have hd := besselRatio_covariance_derivative h 1
  norm_num only [Int.natAbs_one] at hd
  have hf : besselMoment 1=(fun a => besselRatio a 1) := funext (besselMoment_eq 1)
  rw [hf]
  rw [hd.deriv]
  exact mul_pos (by norm_num) (first_cosine_variance_pos h)

theorem besselMoment_polynomial_inverse_bound (h : ℝ) (hh : 0≤h) :
    2*besselMoment 1 h+(besselMoment 1 h)^3≤2*h := by
  have hr := besselMoment_first_le_supersolution h hh
  have hn := besselMoment_nonneg 1 hh
  have hc := pow_le_pow_left₀ hn hr 3
  have hp : 0<1+h^2 := by positivity
  have hspos : 0<Real.sqrt (1+h^2) := Real.sqrt_pos.mpr hp
  have hs := Real.sq_sqrt hp.le
  have he : 2*h-2*(h/Real.sqrt (1+h^2))-(h/Real.sqrt (1+h^2))^3=
      h*(Real.sqrt (1+h^2)-1)^2*(2*Real.sqrt (1+h^2)+1)/(Real.sqrt (1+h^2))^3 := by
    field_simp [hspos.ne']
    nlinarith [congrArg (fun x : ℝ => h*x) hs]
  have hb : 0≤h*(Real.sqrt (1+h^2)-1)^2*(2*Real.sqrt (1+h^2)+1)/(Real.sqrt (1+h^2))^3 := by positivity
  rw [← he] at hb
  linarith

theorem rateAt_quartic_lower (h : ℝ) (hh : 0≤h) :
    (besselMoment 1 h)^2+(besselMoment 1 h)^4/4≤rateAt h := by
  let f : ℝ → ℝ := fun a => rateAt a-(besselMoment 1 a)^2-(besselMoment 1 a)^4/4
  let f' : ℝ → ℝ := fun a =>
    (2*a-2*besselMoment 1 a-(besselMoment 1 a)^3)*deriv (besselMoment 1) a
  have hd (a : ℝ) : HasDerivAt f (f' a) a := by
    have hm := (besselMoment_first_derivative a).differentiableAt.hasDerivAt
    have hi := ((((hasDerivAt_id a).const_mul 2).mul hm).sub
      (log_bessel_derivative a)).sub (hm.pow 2) |>.sub ((hm.pow 4).div_const 4)
    convert hi using 1 <;> try rfl
    dsimp [f']
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr (fun a => (hd a).continuousAt)).continuousOn
      (fun a _ => (hd a).hasDerivWithinAt)
    intro a ha
    have ha0 : 0≤a := mem_Ici.mp (interior_subset ha)
    exact mul_nonneg (by linarith [besselMoment_polynomial_inverse_bound a ha0])
      (besselMoment_first_deriv_pos a).le
  have hz : bessel 0 0=1 := by
    rw [bessel_zero_eq,besselI0Two_eq_circle_integral]
    simp
  have hf0 : f 0=0 := by simp [f,rateAt,besselMoment_one_zero,hz]
  have hb := hm (by simp : (0:ℝ) ∈ Ici 0) hh hh
  rw [hf0] at hb
  dsimp [f] at hb
  linarith

#print axioms rateAt_quartic_lower
end BecknerOnofri.HighDim.CircleScalar

import Legacy.BecknerOnofri.CircleHeatDerivative
import Legacy.BecknerOnofri.CircleHeatDerivativeTail

/-! Actual circle heat monotonicity for t >= 1/4, from a certified complete Fourier derivative tail. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeat
open CircleHeatDerivativeTail

theorem sine_angle_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/2)) : 0 ≤ Real.sin (2*Real.pi*x) := by
  rcases hx with ⟨hx0, hx1⟩
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])

theorem sineTerm_tail_lower {t x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/2)) (m : ℕ) :
    -(Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x))*fourierTerm t m ≤ sineTerm t (m+1) x := by
  have hs := abs_sin_nat_mul_le (m+2) (2*Real.pi*x)
  rw [abs_of_nonneg (sine_angle_nonneg hx)] at hs
  have he : ((m+2:ℕ):ℝ)*(2*Real.pi*x) = 2*Real.pi*((m:ℝ)+2)*x := by push_cast; ring
  rw [he] at hs
  simp only [Nat.cast_add, Nat.cast_ofNat] at hs
  have hn : 0 ≤ (m:ℝ)+2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (neg_abs_le (Real.sin (2*Real.pi*((m:ℝ)+2)*x)))
    (mul_nonneg hn (Real.exp_nonneg (-Real.pi*t*((m:ℝ)+2)^2)))
  have hb := mul_le_mul_of_nonneg_left hs (mul_nonneg hn (Real.exp_nonneg (-Real.pi*t*((m:ℝ)+2)^2)))
  have heq : Real.exp (-Real.pi*t)*Real.exp (-Real.pi*t*(((m:ℝ)+2)^2-1)) =
      Real.exp (-Real.pi*t*((m:ℝ)+2)^2) := by rw [← Real.exp_add]; congr 1; ring
  unfold fourierTerm sineTerm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (m:ℝ)+1+1 = (m:ℝ)+2 by ring]
  have hprod := congrArg (fun r : ℝ => ((m:ℝ)+2)^2*Real.sin (2*Real.pi*x)*r) heq
  nlinarith only [hh, hb, hprod]

theorem sine_series_nonneg_large {t x : ℝ} (ht : 1/4 ≤ t) (hx : x ∈ Icc (0:ℝ) (1/2)) :
    0 ≤ ∑' n : ℕ, sineTerm t n x := by
  have ht0 : 0 < t := by linarith
  have hs := summable_sineTerm ht0 x
  have htail := Summable.tsum_le_tsum (fun m => sineTerm_tail_lower hx m)
    ((summable_fourierTail ht).mul_left (-(Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x))))
    ((summable_nat_add_iff 1).mpr hs)
  rw [tsum_mul_left] at htail
  change -(Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x))*fourierTail t ≤ _ at htail
  have hq : 0 ≤ Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x) := mul_nonneg (Real.exp_nonneg _) (sine_angle_nonneg hx)
  have hb := mul_le_mul_of_nonneg_left (fourierTail_le ht) hq
  have hz : sineTerm t 0 x = Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x) := by simp [sineTerm]
  rw [hs.tsum_eq_zero_add, hz]
  nlinarith only [htail, hb, hq]

theorem deriv_realHeat_nonpos_large {t x : ℝ} (ht : 1/4 ≤ t) (hx : x ∈ Icc (0:ℝ) (1/2)) :
    deriv (realHeat t) x ≤ 0 := by
  rw [(hasDerivAt_realHeat (by linarith : 0 < t) x).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos]) (sine_series_nonneg_large ht hx)

theorem realHeat_antitone_large {t : ℝ} (ht : 1/4 ≤ t) : AntitoneOn (realHeat t) (Icc (0:ℝ) (1/2)) := by
  have ht0 : 0 < t := by linarith
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro x _
    exact (hasDerivAt_realHeat ht0 x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_realHeat ht0 x).differentiableAt.differentiableWithinAt
  · intro x hx
    exact deriv_realHeat_nonpos_large ht (interior_subset hx)

#print axioms realHeat_antitone_large
end Legacy.BecknerOnofri.CircleHeat

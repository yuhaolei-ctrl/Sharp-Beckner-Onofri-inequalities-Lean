import BecknerOnofri.EntropyTailHeat
import BecknerOnofri.RadialThetaTail

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.ThetaDomination

/-- Agreement of the temporal theta convention with the spatial theta at zero. -/
theorem theta_at_zero (s : ℝ) : RadialThetaTail.theta s 0 = realTheta s := by
  unfold RadialThetaTail.theta Legacy.BecknerOnofri.CircleHeat.realHeat
    Legacy.TorusEndpoint.TorusHeatPositivity.theta realTheta
  change (∑' j : ℤ, (Real.exp (-Real.pi*(s/Real.pi)*(j : ℝ)^2) : ℂ) *
    fourier j (0 : UnitAddCircle)).re = _
  simp only [fourier_eval_zero, mul_one, ← Complex.ofReal_tsum, Complex.ofReal_re]
  apply tsum_congr
  intro j
  congr 1
  field_simp

theorem theta_remainder_upper {s : ℝ} (hs : 0 < s) (M : ℕ) :
    realTheta s - (1+2*∑ n ∈ Finset.range M, Real.exp (-s*((n : ℝ)+1)^2)) ≤
      2*Real.exp (-s*((M : ℝ)+1)^2)/(1-Real.exp (-s*(2*(M : ℝ)+3))) := by
  have h := (abs_le.mp (RadialThetaTail.theta_truncation_error hs le_rfl M 0)).2
  simpa only [theta_at_zero, RadialThetaTail.partialTheta, RadialThetaTail.mode,
    mul_zero, Real.cos_zero, mul_one] using h

theorem theta_cube_remainder {s : ℝ} (hs : 0 < s) :
    realTheta s - (1+2*Real.exp (-s)) ≤
      2*Real.exp (-4*s)/(1-Real.exp (-5*s)) := by
  have h := theta_remainder_upper hs 1
  norm_num at h
  ring_nf at h ⊢
  linarith

theorem theta_four_remainder {s : ℝ} (hs : 0 < s) :
    realTheta s - (1+2*Real.exp (-s)) ≤
      2*(Real.exp (-4*s)+Real.exp (-9*s)+Real.exp (-16*s)) +
        2*Real.exp (-25*s)/(1-Real.exp (-11*s)) := by
  have h := theta_remainder_upper hs 4
  norm_num [Finset.sum_range_succ] at h
  ring_nf at h ⊢
  linarith

#print axioms theta_cube_remainder
#print axioms theta_four_remainder
end BecknerOnofri.HighDim.EntropyTail

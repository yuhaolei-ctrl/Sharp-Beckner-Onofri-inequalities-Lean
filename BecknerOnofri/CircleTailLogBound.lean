import BecknerOnofri.CircleBesselSupersolution

/-! The explicit logarithmic comparison used by the manuscript for the
remaining mean range t≥0.999. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem two_log_le_self (z : ℝ) (hz : 0<z) : 2*Real.log z≤z := by
  have hp := Real.sqrt_pos.mpr hz
  have hl := Real.log_le_sub_one_of_pos hp
  rw [Real.log_sqrt hz.le] at hl
  have hs := Real.sq_sqrt hz.le
  nlinarith [sq_nonneg (Real.sqrt z-2)]

theorem tail_log_comparison (t : ℝ) (ht : (999/1000:ℝ)≤t) (ht1 : t<1) :
    Real.log ((1+t)/(1-t))<(13/40)*t/(1-t^2) := by
  have ht0 : 0≤t := by linarith
  have hd : 0<1-t^2 := by nlinarith
  have hm : 0<1-t := by linarith
  let q := (1+t)/(1-t)
  let A := (13/40)*t/(1-t^2)
  have hq : 0<q := div_pos (by linarith) hm
  have hA : 0<A := div_pos (by linarith) hd
  have hs := Real.sq_sqrt hq.le
  have hspos := Real.sqrt_pos.mpr hq
  have hlog := two_log_le_self (Real.sqrt q) hspos
  rw [Real.log_sqrt hq.le] at hlog
  have hden : q*(1-t^2)^2=(1+t)^3*(1-t) := by
    dsimp [q]
    field_simp [hm.ne']
    ring
  have hdenA : A^2*(1-t^2)^2=(13/40:ℝ)^2*t^2 := by
    dsimp [A]
    field_simp [hd.ne']
  have hp : (1+t)^3≤(8:ℝ) := by
    have h := pow_le_pow_left₀ (by linarith : 0≤1+t) (by linarith : 1+t≤2) 3
    norm_num at h
    exact h
  have hx := mul_le_mul_of_nonneg_right hp hm.le
  have ht2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤999/1000) ht 2
  have hprod : q*(1-t^2)^2<A^2*(1-t^2)^2 := by
    rw [hden,hdenA]
    nlinarith
  have hsq : q<A^2 := lt_of_mul_lt_mul_right hprod (sq_nonneg _)
  have hroot : Real.sqrt q<A := by nlinarith
  change Real.log q<A
  linarith

#print axioms tail_log_comparison
end BecknerOnofri.HighDim.CircleScalar

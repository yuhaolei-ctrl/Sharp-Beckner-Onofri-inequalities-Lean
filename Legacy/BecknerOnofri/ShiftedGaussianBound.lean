module

public import Legacy.BecknerOnofri.GaussianTheta
public import Legacy.BecknerOnofri.HeatDensityApproximation

@[expose] public section

/-! Full shifted Gaussian lattice bounds and the actual torus heat kernel. -/

noncomputable section
open scoped BigOperators
open Legacy.TorusEndpoint Legacy.TorusEndpoint.GreenMultiplierSummability

namespace Legacy.BecknerOnofri.ShiftedGaussianBound
open GaussianLattice ThetaDomination TorusHeatPositivity HeatDensityApproximation

def shiftedRadiusSq {d : ℕ} (x : Fin d → ℝ) (k : Frequency d) : ℝ :=
  ∑ i, ((k i : ℝ)-x i)^2

def shiftedGaussian {d : ℕ} (t : ℝ) (x : Fin d → ℝ) (k : Frequency d) : ℝ :=
  Real.exp (-Real.pi/t * shiftedRadiusSq x k)

theorem integer_shift_sq (k : ℤ) {x : ℝ} (hx : |x| ≤ 1/2) :
    (1/4 : ℝ) * (k : ℝ)^2 ≤ ((k : ℝ)-x)^2 := by
  by_cases hk : k = 0
  · subst k
    simpa using sq_nonneg (-x)
  · have hn : 1 ≤ k.natAbs := by omega
    have habs : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hcast : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    have htri := abs_sub_abs_le_abs_sub (k : ℝ) x
    have hhalf : |(k : ℝ)| / 2 ≤ |(k : ℝ)-x| := by linarith
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ |(k : ℝ)|/2) hhalf
    nlinarith [sq_abs (k : ℝ), sq_abs ((k : ℝ)-x)]

theorem shiftedRadiusSq_lower {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1/2) (k : Frequency d) :
    (1/4 : ℝ) * radiusSq k ≤ shiftedRadiusSq x k := by
  unfold radiusSq shiftedRadiusSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => integer_shift_sq (k i) (hx i))

theorem shiftedGaussian_eq_product {d : ℕ} (t : ℝ) (x : Fin d → ℝ) (k : Frequency d) :
    shiftedGaussian t x k = ∏ i, Real.exp (-Real.pi/t * ((k i : ℝ)-x i)^2) := by
  unfold shiftedGaussian shiftedRadiusSq
  rw [Finset.mul_sum, Real.exp_sum]

theorem summable_shiftedGaussian {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    Summable (shiftedGaussian t x) := by
  have hi (i : Fin d) : Summable (fun j : ℤ =>
      ‖(Real.exp (-Real.pi/t * ((j : ℝ)-x i)^2) : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_div] using
      shifted_gaussian_summable (div_pos Real.pi_pos ht) (x i)
  have h := finite_product_summable_norm d
    (fun i j => (Real.exp (-Real.pi/t * ((j : ℝ)-x i)^2) : ℂ)) hi
  simpa only [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
    ← shiftedGaussian_eq_product, shiftedGaussian, abs_of_pos (Real.exp_pos _)] using! h

theorem tsum_shiftedGaussian_eq_product {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    (∑' k, shiftedGaussian t x k) =
      ∏ i, ∑' j : ℤ, Real.exp (-Real.pi/t * ((j : ℝ)-x i)^2) := by
  have hi (i : Fin d) : Summable (fun j : ℤ =>
      ‖(Real.exp (-Real.pi/t * ((j : ℝ)-x i)^2) : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_div] using
      shifted_gaussian_summable (div_pos Real.pi_pos ht) (x i)
  have hc := finite_product_tsum d
    (fun i j => (Real.exp (-Real.pi/t * ((j : ℝ)-x i)^2) : ℂ)) hi
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_tsum] at hc
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, shiftedGaussian_eq_product] using hr

theorem shiftedGaussian_le {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1/2) (k : Frequency d) :
    shiftedGaussian t x k ≤ gaussian (Real.pi/(4*t)) k := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (shiftedRadiusSq_lower x hx k)
    (div_pos Real.pi_pos ht).le
  change -Real.pi/t * shiftedRadiusSq x k ≤ -(Real.pi/(4*t)) * radiusSq k
  have he : Real.pi/(4*t) = (Real.pi/t)*(1/4) := by ring
  rw [he]
  convert! neg_le_neg h using 1 <;> ring

/-- Exact zero-mode separation with an absolutely convergent Gaussian bound. -/
theorem tsum_shiftedGaussian_le {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1/2) :
    (∑' k, shiftedGaussian t x k) ≤
      Real.exp (-Real.pi/t * ∑ i, (x i)^2) + realTheta (Real.pi/(4*t))^d - 1 := by
  classical
  have hsplit := (summable_shiftedGaussian ht x).tsum_eq_add_tsum_ite (0 : Frequency d)
  have hzero : shiftedGaussian t x (0 : Frequency d) =
      Real.exp (-Real.pi/t * ∑ i, (x i)^2) := by simp [shiftedGaussian, shiftedRadiusSq]
  have hsum : Summable (fun k : Frequency d => if k = 0 then 0 else shiftedGaussian t x k) := by
    apply ((summable_shiftedGaussian ht x).indicator {k | k ≠ 0}).congr
    intro k
    by_cases hk : k = 0 <;> simp [Set.indicator, hk]
  have htail : (∑' k : Frequency d, if k = 0 then 0 else shiftedGaussian t x k) ≤
      realTheta (Real.pi/(4*t))^d - 1 := by
    rw [← tsum_nonzeroGaussian_eq_theta_pow_sub_one d (div_pos Real.pi_pos (by positivity))]
    apply Summable.tsum_le_tsum _ hsum (summable_nonzeroGaussian (by positivity))
    intro k
    by_cases hk : k = 0
    · simp [hk, nonzeroGaussian]
    · simpa only [if_neg hk, nonzeroGaussian] using shiftedGaussian_le ht x hx k
  rw [hsplit, hzero]
  linarith

theorem heatKernel_eq_shiftedGaussian {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    heatKernel t (fun i => (x i : UnitAddCircle)) =
      t^(-(d : ℝ)/2) * ∑' k, shiftedGaussian t x k := by
  unfold heatKernel
  rw [torusTheta_eq_ofReal_product ht, Complex.ofReal_re]
  simp_rw [theta_coe_eq_shifted_gaussian ht, Complex.ofReal_re]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [tsum_shiftedGaussian_eq_product ht x]
  congr 1
  rw [one_div, ← Real.rpow_neg ht.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- The actual heat kernel satisfies the separated zero-image upper bound. -/
theorem heatKernel_le {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1/2) :
    heatKernel t (fun i => (x i : UnitAddCircle)) ≤
      t^(-(d : ℝ)/2) * (Real.exp (-Real.pi/t * ∑ i, (x i)^2) +
        realTheta (Real.pi/(4*t))^d - 1) := by
  rw [heatKernel_eq_shiftedGaussian ht x]
  exact mul_le_mul_of_nonneg_left (tsum_shiftedGaussian_le ht x hx) (Real.rpow_pos_of_pos ht _).le

#print axioms shiftedRadiusSq_lower
#print axioms tsum_shiftedGaussian_le
#print axioms heatKernel_eq_shiftedGaussian
#print axioms heatKernel_le
end Legacy.BecknerOnofri.ShiftedGaussianBound

module

public import Legacy.TorusEndpoint.EndpointSharpnessHeat

@[expose] public section

/-! # Row S006 (input to the concentration test): a Gaussian lower bound for the heat kernel

For `t > 0` the periodic heat kernel `θ_t(x) = ∑_{k ∈ ℤ^d} e^{-π t |k|²} e^{2π i k·x}` of the torus has
the Poisson representation `θ_t(x) = t^{-d/2} ∑_{n ∈ ℤ^d} e^{-π |n - x|²/t}` (reused:
`Legacy.TorusEndpoint.TorusHeatPositivity.theta_coe_eq_shifted_gaussian`).  Keeping the single
summand that realizes the distance from `x` to the lattice gives

  `θ_t(x) ≥ t^{-d/2} exp(-π (∑_j ‖x_j‖²)/t)`,

where `‖x_j‖` is the distance in the circle `ℝ/ℤ` to `0`.  This is the lower bound that replaces, in
the localized concentration test, the Robin-constant asymptotics of the Green function. -/

noncomputable section
open Real

namespace BecknerOnofri.V2.Reaudit.Obstruction

open Legacy.TorusEndpoint Legacy.TorusEndpoint.TorusHeatPositivity

/-- One-dimensional Gaussian lower bound for the heat kernel of the circle. -/
theorem theta_re_ge_gaussian {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    (t ^ (1 / 2 : ℝ))⁻¹ * Real.exp (-Real.pi * ‖x‖ ^ 2 / t) ≤ (theta t x).re := by
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [theta_coe_eq_shifted_gaussian ht, Complex.ofReal_re]
    have hs : Summable (fun n : ℤ => Real.exp (-Real.pi / t * ((n : ℝ) - y) ^ 2)) := by
      simpa only [neg_div] using shifted_gaussian_summable (div_pos Real.pi_pos ht) y
    have hle := hs.le_tsum (round y) (fun n _ => (Real.exp_pos _).le)
    have hn : ‖(y : UnitAddCircle)‖ = |y - round y| := UnitAddCircle.norm_eq
    have h1 : -Real.pi * ‖(y : UnitAddCircle)‖ ^ 2 / t = -Real.pi / t * ((round y : ℝ) - y) ^ 2 := by
      rw [hn, sq_abs]
      ring
    rw [h1, one_div (t ^ (1 / 2 : ℝ))]
    exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Real.rpow_nonneg ht.le _))

/-- Gaussian lower bound for the heat kernel of the `d`-torus. -/
theorem torusTheta_re_ge_gaussian {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    t ^ (-(d : ℝ) / 2) * Real.exp (-Real.pi * (∑ j : Fin d, ‖x j‖ ^ 2) / t) ≤
      (torusTheta t x).re := by
  rw [torusTheta_eq_ofReal_product ht, Complex.ofReal_re]
  have e1 : t ^ (-(d : ℝ) / 2) = ((t ^ (1 / 2 : ℝ))⁻¹) ^ d := by
    rw [← Real.rpow_neg ht.le, ← Real.rpow_mul_natCast ht.le]
    congr 1
    ring
  have e2 : -Real.pi * (∑ j : Fin d, ‖x j‖ ^ 2) / t =
      ∑ j : Fin d, (-Real.pi * ‖x j‖ ^ 2 / t) := by
    rw [Finset.mul_sum, Finset.sum_div]
  have hprod : t ^ (-(d : ℝ) / 2) * Real.exp (-Real.pi * (∑ j : Fin d, ‖x j‖ ^ 2) / t) =
      ∏ j : Fin d, ((t ^ (1 / 2 : ℝ))⁻¹ * Real.exp (-Real.pi * ‖x j‖ ^ 2 / t)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, e1, e2]
  rw [hprod]
  exact Finset.prod_le_prod₀
    (fun j _ => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le)
    (fun j _ => theta_re_ge_gaussian ht (x j))

end BecknerOnofri.V2.Reaudit.Obstruction

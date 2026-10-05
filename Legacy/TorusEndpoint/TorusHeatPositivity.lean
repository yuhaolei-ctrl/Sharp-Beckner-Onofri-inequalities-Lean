import Legacy.TorusEndpoint.TorusFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Strict pointwise positivity of the unit-circle Fourier heat kernel

The series uses the actual unit-circle characters and multiplier exp(-pi t n^2).
Its shifted-Gaussian representation is proved for every real representative.
This module does not construct a Green kernel or perform a Mellin integral.
-/

open scoped BigOperators Topology
open Filter

namespace Legacy.TorusEndpoint.TorusHeatPositivity

/-- A real Gaussian with an arbitrary real linear perturbation is summable on Z. -/
theorem gaussian_quadratic_summable {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable (fun n : ℤ => Real.exp (-a * (n : ℝ)^2 + b * n)) := by
  have hd := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
    (a := (-a : ℝ)) (by simpa using neg_neg_of_pos ha) (b : ℂ) (-2)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    (hd.comp_tendsto Int.tendsto_coe_cofinite)
  have hr := (Complex.hasSum_re hs.hasSum).summable
  simpa only [Function.comp_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, ← Complex.ofReal_exp, Complex.ofReal_re] using hr

theorem shifted_gaussian_summable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-a * ((n : ℝ) - x)^2)) := by
  have hs := (gaussian_quadratic_summable ha (2 * a * x)).mul_left (Real.exp (-a * x^2))
  apply hs.congr
  intro n
  rw [← Real.exp_add]
  congr 1
  ring

noncomputable def theta (t : ℝ) (x : UnitAddCircle) : ℂ :=
  ∑' n : ℤ, (Real.exp (-Real.pi * t * (n : ℝ)^2) : ℂ) * fourier n x

theorem theta_weights_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ)^2)) := by
  simpa only [zero_mul, add_zero, neg_mul] using
    gaussian_quadratic_summable (mul_pos Real.pi_pos ht) 0

theorem theta_terms_norm {t : ℝ} (x : UnitAddCircle) (n : ℤ) :
    ‖(Real.exp (-Real.pi * t * (n : ℝ)^2) : ℂ) * fourier n x‖ =
      Real.exp (-Real.pi * t * (n : ℝ)^2) := by
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem theta_summable {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    Summable (fun n : ℤ => (Real.exp (-Real.pi * t * (n : ℝ)^2) : ℂ) * fourier n x) := by
  apply (theta_weights_summable ht).of_norm_bounded
  intro n
  exact (theta_terms_norm x n).le

theorem theta_continuous {t : ℝ} (ht : 0 < t) : Continuous (theta t) := by
  apply continuous_tsum (fun n => continuous_const.mul (fourier n).continuous)
    (theta_weights_summable ht)
  intro n x
  exact (theta_terms_norm x n).le

/-- Exact Poisson representation, including the positive-real square-root branch. -/
theorem theta_coe_eq_shifted_gaussian {t : ℝ} (ht : 0 < t) (x : ℝ) :
    theta t (x : UnitAddCircle) =
      ((1 / t ^ (1 / 2 : ℝ) *
        ∑' n : ℤ, Real.exp (-Real.pi / t * ((n : ℝ) - x)^2) : ℝ) : ℂ) := by
  have hp := Complex.tsum_exp_neg_quadratic
    (a := (t : ℂ)) (by simpa using ht) (Complex.I * x)
  have hi : Complex.I * (Complex.I * (x : ℂ)) = -(x : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  calc
    theta t (x : UnitAddCircle) =
        ∑' n : ℤ, Complex.exp (-Real.pi * (t : ℂ) * (n : ℂ)^2 +
          2 * Real.pi * (Complex.I * x) * n) := by
      apply tsum_congr
      intro n
      rw [fourier_coe_apply]
      simp only [Complex.ofReal_one, div_one, Complex.ofReal_exp]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [hp, hi]
      have hpow : ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
        simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
          Complex.ofReal_cpow ht.le (1 / 2)
      rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, hpow]
      congr 1
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro n
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring

theorem theta_coe_re_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < (theta t (x : UnitAddCircle)).re := by
  rw [theta_coe_eq_shifted_gaussian ht, Complex.ofReal_re]
  apply mul_pos
  · exact one_div_pos.mpr (Real.rpow_pos_of_pos ht _)
  · simpa only [neg_div] using
      (shifted_gaussian_summable (div_pos Real.pi_pos ht) x).tsum_pos
        (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

theorem theta_re_pos {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    0 < (theta t x).re := by
  induction x using QuotientAddGroup.induction_on
  exact theta_coe_re_pos ht _

theorem theta_im_zero {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    (theta t x).im = 0 := by
  induction x using QuotientAddGroup.induction_on
  rw [theta_coe_eq_shifted_gaussian ht]
  exact Complex.ofReal_im _

theorem theta_eq_ofReal_re {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    theta t x = ((theta t x).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [theta_im_zero ht]

/-- Absolute summability of the product family over an actual finite-dimensional lattice. -/
theorem finite_product_summable_norm (d : ℕ) (f : Fin d → ℤ → ℂ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun k : Frequency d => ‖∏ i : Fin d, f i (k i)‖) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    have hs := (hf 0).mul_of_nonneg (ih (fun i => f i.succ) (fun i => hf i.succ))
      (fun n => norm_nonneg _) (fun k => norm_nonneg _)
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv, norm_mul] using hs

/-- The genuine lattice sum is the product of the one-dimensional sums. -/
theorem finite_product_tsum (d : ℕ) (f : Fin d → ℤ → ℂ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    (∑' k : Frequency d, ∏ i : Fin d, f i (k i)) =
      ∏ i : Fin d, ∑' n : ℤ, f i n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).tsum_eq]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← tsum_mul_tsum_of_summable_norm (hf 0)
      (finite_product_summable_norm d (fun i => f i.succ) (fun i => hf i.succ))]
    rw [ih (fun i => f i.succ) (fun i => hf i.succ)]

noncomputable def torusTheta {d : ℕ} (t : ℝ) (x : Torus d) : ℂ :=
  ∑' k : Frequency d, (Real.exp (-Real.pi * t *
    (∑ j : Fin d, (k j : ℝ)^2)) : ℂ) * UnitAddTorus.mFourier k x

theorem torusTheta_term_eq_product {d : ℕ} (t : ℝ) (x : Torus d) (k : Frequency d) :
    (Real.exp (-Real.pi * t * (∑ j : Fin d, (k j : ℝ)^2)) : ℂ) *
      UnitAddTorus.mFourier k x =
    ∏ j : Fin d, (Real.exp (-Real.pi * t * (k j : ℝ)^2) : ℂ) * fourier (k j) (x j) := by
  rw [Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]

theorem torusTheta_summable {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Summable (fun k : Frequency d => (Real.exp (-Real.pi * t *
      (∑ j : Fin d, (k j : ℝ)^2)) : ℂ) * UnitAddTorus.mFourier k x) := by
  simp_rw [torusTheta_term_eq_product]
  have hf (i : Fin d) : Summable (fun n : ℤ =>
      ‖(Real.exp (-Real.pi * t * (n : ℝ)^2) : ℂ) * fourier n (x i)‖) := by
    simpa only [theta_terms_norm] using theta_weights_summable ht
  exact (finite_product_summable_norm d
    (fun i n => (Real.exp (-Real.pi * t * (n : ℝ)^2) : ℂ) * fourier n (x i)) hf).of_norm

theorem torusTheta_eq_product {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    torusTheta t x = ∏ j : Fin d, theta t (x j) := by
  unfold torusTheta theta
  simp_rw [torusTheta_term_eq_product]
  apply finite_product_tsum d
    (fun i n => (Real.exp (-Real.pi * t * (n : ℝ)^2) : ℂ) * fourier n (x i))
  intro i
  simpa only [theta_terms_norm] using theta_weights_summable ht

theorem torusTheta_eq_ofReal_product {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    torusTheta t x = ((∏ j : Fin d, (theta t (x j)).re : ℝ) : ℂ) := by
  rw [torusTheta_eq_product ht, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun j _ => theta_eq_ofReal_re ht (x j))

theorem torusTheta_re_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    0 < (torusTheta t x).re := by
  rw [torusTheta_eq_ofReal_product ht, Complex.ofReal_re]
  exact Finset.prod_pos (fun j _ => theta_re_pos ht (x j))

theorem torusTheta_im_zero {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    (torusTheta t x).im = 0 := by
  rw [torusTheta_eq_ofReal_product ht]
  exact Complex.ofReal_im _

end Legacy.TorusEndpoint.TorusHeatPositivity

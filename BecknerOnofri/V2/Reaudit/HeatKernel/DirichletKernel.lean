module

public import Legacy.BecknerOnofri.CircleDirichletHeat
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

/-! # The Dirichlet heat kernel on the half-period `(0,1/2)` (U05/S015 prerequisite)

The printed proof of `prop:cosine-all` uses, for the Dirichlet Laplacian `P_D` on `(0,1/2)`
(with Lebesgue measure), the integral kernel `p_t^D` of `e^{-t P_D}`.  Its spectral decomposition
is explicit: `P_D` has the orthonormal eigenfunctions `φ_n(x) = 2 sin(2π n x)` (`n ≥ 1`) with
eigenvalues `(2π n)²`.  Here the kernel is **defined by this eigenfunction expansion**

`p_t^D(a,b) = ∑_{n ≥ 1} e^{-(2πn)² t} φ_n(a) φ_n(b)`

and the facts the printed argument uses are proved:

* orthonormality of the `φ_n` and `∫ p_t^D(a,b) φ_m(b) db = e^{-(2πm)² t} φ_m(a)`
  (the kernel acts as `e^{-tP_D}` on the eigenbasis), symmetry, and the semigroup law
  (Chapman–Kolmogorov) `p_{t+s}^D = ∫ p_t^D p_s^D`;
* the reflection formula `p_t^D(a,b) = p_t^{per}(a-b) - p_t^{per}(a+b)` for the circle heat kernel
  (`eq:reflected-circle-heat-comparison`);
* strict positivity `p_t^D(a,b) > 0` for `t > 0`, `a,b ∈ (0,1/2)` (`eq:dirichlet-heat-positive`
  for one interval factor) and the strict comparison `p_t^D(a,b) < p_t^{per}(a-b)`.

Reused (generic theta-function facts from the legacy tree): strict decrease of the circle heat
kernel on `[0,1/2]` (`Legacy.BecknerOnofri.CircleHeat.realHeat_strictAnti`) and the
legacy `dirichletHeat`.  The time scale of the legacy `realHeat τ` is `τ = 4π t`.
-/

noncomputable section
open Set Filter MeasureTheory intervalIntegral Topology
open scoped Real
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri.CircleHeat

/-- The manuscript's circle heat kernel
`p_t(x) = ∑_{n∈ℤ} e^{-4π² n² t} e^{2π i n x}` (`eq:coordinate-circle-heat-kernel`), through the
repository's `realHeat` (time scale `τ = 4π t`). -/
def circleKernel (t x : ℝ) : ℝ := realHeat (4 * π * t) x

/-- `p_t(x) = 1 + 2 ∑_{n ≥ 1} e^{-4π² n² t} cos(2π n x)`. -/
theorem circleKernel_eq_cosine_series {t : ℝ} (ht : 0 < t) (x : ℝ) :
    circleKernel t x =
      1 + 2 * ∑' n : ℕ, Real.exp (-(4 * π ^ 2) * ((n : ℝ) + 1) ^ 2 * t) *
        Real.cos (2 * π * ((n : ℝ) + 1) * x) := by
  unfold circleKernel
  rw [realHeat_eq_cosine_series (by positivity)]
  unfold cosineTerm
  congr 3
  funext n
  congr 2
  ring_nf

/-- The `n`-th Dirichlet eigenfunction of `(0,1/2)` is `φ_{n+1}(x) = 2 sin(2π (n+1) x)`. -/
def dirichletEig (n : ℕ) (x : ℝ) : ℝ := 2 * Real.sin (2 * π * ((n : ℝ) + 1) * x)

/-- The corresponding eigenvalue `(2π (n+1))²`. -/
def dirichletEigval (n : ℕ) : ℝ := (2 * π * ((n : ℝ) + 1)) ^ 2

/-- The Dirichlet heat kernel of `(0,1/2)`, defined by the eigenfunction expansion. -/
def dirichletKernel (t a b : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b

theorem dirichletEigval_pos (n : ℕ) : 0 < dirichletEigval n := by
  unfold dirichletEigval; positivity

theorem dirichletEig_abs_le (n : ℕ) (x : ℝ) : |dirichletEig n x| ≤ 2 := by
  unfold dirichletEig
  rw [abs_mul, abs_two]
  nlinarith [Real.abs_sin_le_one (2 * π * ((n : ℝ) + 1) * x)]

theorem summable_dirichlet_weights {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-dirichletEigval n * t)) := by
  have hs := summable_polynomial_gaussian_succ (mul_pos Real.pi_pos (by positivity : 0 < 4 * π * t)) 0
  simp only [pow_zero, one_mul, neg_mul] at hs
  refine hs.congr (fun n => ?_)
  unfold dirichletEigval
  congr 1
  ring

theorem dirichletKernel_term_abs_le (t : ℝ) (n : ℕ) (a b : ℝ) :
    |Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b| ≤
      4 * Real.exp (-dirichletEigval n * t) := by
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := dirichletEig_abs_le n a
  have h2 := dirichletEig_abs_le n b
  have h3 : |dirichletEig n a| * |dirichletEig n b| ≤ 4 := by
    nlinarith [abs_nonneg (dirichletEig n a), abs_nonneg (dirichletEig n b)]
  have := Real.exp_pos (-dirichletEigval n * t)
  nlinarith

theorem summable_dirichletKernel {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    Summable (fun n : ℕ => Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b) :=
  Summable.of_norm_bounded ((summable_dirichlet_weights ht).mul_left 4)
    (fun n => by simpa only [Real.norm_eq_abs] using dirichletKernel_term_abs_le t n a b)

/-- Comparison with the legacy `dirichletHeat` (time scale `τ = 4π t`). -/
theorem dirichletKernel_eq_dirichletHeat {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    dirichletKernel t a b = dirichletHeat (4 * π * t) a b := by
  rw [dirichletHeat_eq_sine_series (by positivity)]
  unfold dirichletKernel
  rw [← tsum_mul_left]
  congr 1
  funext n
  unfold dirichletEig dirichletEigval
  have : Real.exp (-(2 * π * ((n : ℝ) + 1)) ^ 2 * t) = Real.exp (-π * (4 * π * t) * ((n : ℝ) + 1) ^ 2) := by
    congr 1; ring
  rw [this]
  ring

/-- **Reflection formula** (`eq:reflected-circle-heat-comparison`):
`p_t^D(a,b) = p_t^{per}(a-b) - p_t^{per}(a+b)`. -/
theorem dirichletKernel_eq_reflection {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    dirichletKernel t a b = circleKernel t (a - b) - circleKernel t (a + b) := by
  rw [dirichletKernel_eq_dirichletHeat ht]
  rfl

theorem dirichletKernel_symm {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    dirichletKernel t a b = dirichletKernel t b a := by
  unfold dirichletKernel
  congr 1; funext n; ring

theorem dirichletKernel_zero_left {t : ℝ} (ht : 0 < t) (b : ℝ) : dirichletKernel t 0 b = 0 := by
  unfold dirichletKernel dirichletEig
  simp

theorem dirichletKernel_half_left {t : ℝ} (ht : 0 < t) (b : ℝ) : dirichletKernel t (1 / 2) b = 0 := by
  have h0 : ∀ n : ℕ, dirichletEig n (1 / 2) = 0 := by
    intro n
    unfold dirichletEig
    have : 2 * π * ((n : ℝ) + 1) * (1 / 2) = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
    rw [this, Real.sin_nat_mul_pi, mul_zero]
  unfold dirichletKernel
  simp only [h0, mul_zero, zero_mul, tsum_zero]

theorem dirichletKernel_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (fun p : ℝ × ℝ => dirichletKernel t p.1 p.2) := by
  rw [show (fun p : ℝ × ℝ => dirichletKernel t p.1 p.2) =
      fun p : ℝ × ℝ => dirichletHeat (4 * π * t) p.1 p.2 from by
    funext p; exact dirichletKernel_eq_dirichletHeat ht p.1 p.2]
  exact dirichletHeat_continuous (by positivity)

/-- **Strict positivity** of the Dirichlet heat kernel (`eq:dirichlet-heat-positive`, one interval
factor): `p_t^D(a,b) > 0` for `t > 0` and `a,b ∈ (0,1/2)`. -/
theorem dirichletKernel_pos {t a b : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) (1 / 2))
    (hb : b ∈ Ioo (0 : ℝ) (1 / 2)) : 0 < dirichletKernel t a b := by
  rw [dirichletKernel_eq_dirichletHeat ht]
  exact dirichletHeat_pos (by positivity) ha hb

theorem dirichletKernel_nonneg {t a b : ℝ} (ht : 0 < t) (ha : a ∈ Icc (0 : ℝ) (1 / 2))
    (hb : b ∈ Icc (0 : ℝ) (1 / 2)) : 0 ≤ dirichletKernel t a b := by
  rw [dirichletKernel_eq_dirichletHeat ht]
  exact dirichletHeat_nonneg (by positivity) ha hb

/-- **Dirichlet versus periodic** (`eq:reflected-circle-heat-comparison`, right inequality):
`p_t^D(a,b) < p_t^{per}(a-b)`. -/
theorem dirichletKernel_lt_circleKernel {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    dirichletKernel t a b < circleKernel t (a - b) := by
  rw [dirichletKernel_eq_dirichletHeat ht]
  exact dirichletHeat_lt_periodic (by positivity) a b

theorem circleKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < circleKernel t x := by
  unfold circleKernel realHeat
  exact Legacy.TorusEndpoint.TorusHeatPositivity.theta_re_pos (by positivity) _

/-! ### The eigenbasis -/

theorem integral_cos_two_pi_int_mul (k : ℤ) :
    ∫ x in (0 : ℝ)..(1 / 2), Real.cos (2 * π * (k : ℝ) * x) = if k = 0 then 1 / 2 else 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * π * (k : ℝ)) ≠ 0 := by positivity
    rw [if_neg hk, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have e : 2 * π * (k : ℝ) * (1 / 2) = (k : ℝ) * π := by ring
    rw [mul_zero, e, Real.sin_int_mul_pi, Real.sin_zero]
    simp

/-- Orthonormality of the Dirichlet eigenfunctions in `L²(0,1/2)`. -/
theorem integral_dirichletEig_mul (m n : ℕ) :
    ∫ x in (0 : ℝ)..(1 / 2), dirichletEig m x * dirichletEig n x = if m = n then 1 else 0 := by
  have key : ∀ x : ℝ, dirichletEig m x * dirichletEig n x =
      2 * Real.cos (2 * π * (((m : ℤ) - n : ℤ) : ℝ) * x) -
        2 * Real.cos (2 * π * (((m : ℤ) + n + 2 : ℤ) : ℝ) * x) := by
    intro x
    unfold dirichletEig
    have h1 : 2 * π * (((m : ℤ) - n : ℤ) : ℝ) * x =
        2 * π * ((m : ℝ) + 1) * x - 2 * π * ((n : ℝ) + 1) * x := by push_cast; ring
    have h2 : 2 * π * (((m : ℤ) + n + 2 : ℤ) : ℝ) * x =
        2 * π * ((m : ℝ) + 1) * x + 2 * π * ((n : ℝ) + 1) * x := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [key]
  have i1 : IntervalIntegrable (fun x : ℝ => Real.cos (2 * π * (((m : ℤ) - n : ℤ) : ℝ) * x)) volume 0 (1 / 2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => Real.cos (2 * π * (((m : ℤ) + n + 2 : ℤ) : ℝ) * x)) volume 0 (1 / 2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.const_mul 2) (i2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_two_pi_int_mul, integral_cos_two_pi_int_mul]
  have hne : ((m : ℤ) + n + 2 : ℤ) ≠ 0 := by omega
  rw [if_neg hne]
  by_cases hmn : m = n
  · subst hmn; simp
  · have : ((m : ℤ) - n : ℤ) ≠ 0 := by omega
    rw [if_neg this, if_neg hmn]; simp

end BecknerOnofri.V2.Reaudit.HeatKernel

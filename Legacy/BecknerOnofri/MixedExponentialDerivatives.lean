module

public import Legacy.BecknerOnofri.MixedExponentialCalculus
public import Legacy.BecknerOnofri.MixedExponentialTerms
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-! The actual ordered mixed derivatives of exp(u), with an explicit positive Bell remainder. -/
noncomputable section
open Set
open scoped ContDiff
namespace Legacy.BecknerOnofri.MixedExponentialDerivatives
open FiniteDifferences

/-- Evaluation of a Bell monomial in actual mixed partial derivatives. -/
def evalMonomial {d : ℕ} (u : Space d → ℝ) : Monomial d → Space d → ℝ
  | [], _ => 1
  | b :: bs, x => mixedPartial b u x * evalMonomial u bs x

/-- Evaluation of a finite list of monomials; multiplicities are positive integer coefficients. -/
def evalTerms {d : ℕ} (u : Space d → ℝ) : Terms d → Space d → ℝ
  | [], _ => 0
  | q :: qs, x => evalMonomial u q x + evalTerms u qs x

theorem evalTerms_append {d : ℕ} (u : Space d → ℝ) (ps qs : Terms d) (x : Space d) :
    evalTerms u (ps ++ qs) x = evalTerms u ps x + evalTerms u qs x := by
  induction ps with
  | nil => simp [evalTerms]
  | cons p ps ih => simp [evalTerms, ih, add_assoc]

theorem evalTerms_map_cons {d : ℕ} (u : Space d → ℝ) (b : Block d) (ps : Terms d) (x : Space d) :
    evalTerms u (ps.map (fun q => b :: q)) x = mixedPartial b u x * evalTerms u ps x := by
  induction ps with
  | nil => simp [evalTerms]
  | cons p ps ih => simp [evalTerms, evalMonomial, ih, mul_add]

theorem eval_stepTerms {d : ℕ} (u : Space d → ℝ) (i : Fin d) (ps : Terms d) (x : Space d) :
    evalTerms u (stepTerms i ps) x =
      mixedPartial [i] u x * evalTerms u ps x +
        evalTerms u (ps.flatMap (differentiateMonomial i)) x := by
  induction ps with
  | nil => simp [stepTerms, evalTerms]
  | cons p ps ih =>
    simp only [stepTerms, List.flatMap_cons, evalTerms_append, evalTerms, evalMonomial] at ih ⊢
    rw [ih]
    ring

theorem evalMonomial_contDiffOn {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (bs : Monomial d) :
    ContDiffOn ℝ ∞ (evalMonomial u bs) (closedCube d) := by
  induction bs with
  | nil => exact contDiffOn_const
  | cons b bs ih => exact (contDiffOn_mixedPartial hu b).mul ih

theorem evalTerms_contDiffOn {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (ps : Terms d) :
    ContDiffOn ℝ ∞ (evalTerms u ps) (closedCube d) := by
  induction ps with
  | nil => exact contDiffOn_const
  | cons p ps ih => exact (evalMonomial_contDiffOn hu p).add ih

/-- Exact list Leibniz differentiation for products of the actual ordered derivatives. -/
theorem derivative_evalMonomial {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (i : Fin d) (bs : Monomial d)
    {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (evalMonomial u bs) x = evalTerms u (differentiateMonomial i bs) x := by
  induction bs with
  | nil => exact coordinateDerivative_const i 1 x
  | cons b bs ih =>
    change coordinateDerivative i (fun y => mixedPartial b u y * evalMonomial u bs y) x = _
    rw [coordinateDerivative_mul i (contDiffOn_mixedPartial hu b) (evalMonomial_contDiffOn hu bs) hx,
      ih, ← mixedPartial_append_single]
    simp only [differentiateMonomial, evalTerms, evalMonomial, evalTerms_map_cons]

theorem derivative_evalTerms {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (i : Fin d) (ps : Terms d)
    {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (evalTerms u ps) x =
      evalTerms u (ps.flatMap (differentiateMonomial i)) x := by
  induction ps with
  | nil => exact coordinateDerivative_const i 0 x
  | cons p ps ih =>
    change coordinateDerivative i (fun y => evalMonomial u p y + evalTerms u ps y) x = _
    rw [coordinateDerivative_add i (evalMonomial_contDiffOn hu p) (evalTerms_contDiffOn hu ps) hx,
      derivative_evalMonomial hu i p hx, ih]
    exact (evalTerms_append u _ _ x).symm

/-- The actual chain rule of every positive order. No mixed-partial symmetry is used. -/
theorem mixedPartial_exp_formula {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (is : List (Fin d)) (his : is ≠ [])
    {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial is (fun y => Real.exp (u y)) x =
      Real.exp (u x) * (mixedPartial is u x + evalTerms u (remainderTerms is) x) := by
  induction is using List.reverseRecOn generalizing x with
  | nil => exact (his rfl).elim
  | append_singleton is i ih =>
    by_cases hi0 : is = []
    · subst is
      simpa only [List.nil_append, remainderTerms_single, evalTerms, add_zero] using
        mixedPartial_exp_one i hu hx
    · have he : EqOn (mixedPartial is (fun y => Real.exp (u y)))
          (fun y => Real.exp (u y) * (mixedPartial is u y + evalTerms u (remainderTerms is) y))
          (closedCube d) := fun y hy => ih hi0 hy
      rw [mixedPartial_append_single,
        coordinateDerivative_congr i he hx,
        coordinateDerivative_mul i hu.exp
          ((contDiffOn_mixedPartial hu is).add (evalTerms_contDiffOn hu (remainderTerms is))) hx,
        coordinateDerivative_exp i hu hx,
        coordinateDerivative_add i (contDiffOn_mixedPartial hu is)
          (evalTerms_contDiffOn hu (remainderTerms is)) hx,
        ← mixedPartial_append_single, derivative_evalTerms hu i (remainderTerms is) hx,
        remainderTerms_snoc is i hi0]
      simp only [evalTerms, evalMonomial]
      rw [eval_stepTerms]
      simp only [mixedPartial_cons, mixedPartial_nil]
      ring

/-- Every Bell term is a finite product of actual lower-order derivatives. -/
theorem evalMonomial_nonneg {d n : ℕ} (u : Space d → ℝ) (x : Space d) (bs : Monomial d)
    (hbs : Admissible n bs)
    (hpos : ∀ js : List (Fin d), 0 < js.length → js.length < n → 0 ≤ mixedPartial js u x) :
    0 ≤ evalMonomial u bs x := by
  induction bs with
  | nil => norm_num [evalMonomial]
  | cons b bs ih =>
    have hb := hbs b (by simp)
    exact mul_nonneg (hpos b hb.1 hb.2) (ih (fun q hq => hbs q (by simp [hq])))

theorem evalTerms_nonneg {d n : ℕ} (u : Space d → ℝ) (x : Space d) (ps : Terms d)
    (hps : ∀ q ∈ ps, Admissible n q)
    (hpos : ∀ js : List (Fin d), 0 < js.length → js.length < n → 0 ≤ mixedPartial js u x) :
    0 ≤ evalTerms u ps x := by
  induction ps with
  | nil => norm_num [evalTerms]
  | cons p ps ih =>
    exact add_nonneg (evalMonomial_nonneg u x p (hps p (by simp)) hpos)
      (ih (fun q hq => hps q (by simp [hq])))

/-- The polynomial part of the remainder has nonnegative coefficients and uses only lower orders. -/
theorem bell_remainder_nonneg {d : ℕ} (u : Space d → ℝ) (is : List (Fin d)) (x : Space d)
    (hpos : ∀ js : List (Fin d), 0 < js.length → js.length < is.length → 0 ≤ mixedPartial js u x) :
    0 ≤ evalTerms u (remainderTerms is) x :=
  evalTerms_nonneg u x _ (remainderTerms_admissible is) hpos

/-- The non-leading part of the actual derivative, including the positive exponential factor. -/
def remainder {d : ℕ} (u : Space d → ℝ) (is : List (Fin d)) (x : Space d) : ℝ :=
  Real.exp (u x) * evalTerms u (remainderTerms is) x

theorem mixedPartial_exp_eq_leading_add {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (is : List (Fin d)) (his : is ≠ [])
    {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial is (fun y => Real.exp (u y)) x =
      Real.exp (u x) * mixedPartial is u x + remainder u is x := by
  rw [mixedPartial_exp_formula hu is his hx]
  exact mul_add _ _ _

theorem remainder_nonneg {d : ℕ} (u : Space d → ℝ) (is : List (Fin d)) (x : Space d)
    (hpos : ∀ js : List (Fin d), 0 < js.length → js.length < is.length → 0 ≤ mixedPartial js u x) :
    0 ≤ remainder u is x :=
  mul_nonneg (Real.exp_pos _).le (bell_remainder_nonneg u is x hpos)

theorem mixedPartial_exp_ge_leading {d : ℕ} {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) (is : List (Fin d)) (his : is ≠ [])
    {x : Space d} (hx : x ∈ closedCube d)
    (hpos : ∀ js : List (Fin d), 0 < js.length → js.length < is.length → 0 ≤ mixedPartial js u x) :
    Real.exp (u x) * mixedPartial is u x ≤ mixedPartial is (fun y => Real.exp (u y)) x := by
  rw [mixedPartial_exp_eq_leading_add hu is his hx]
  exact le_add_of_nonneg_right (remainder_nonneg u is x hpos)

#print axioms mixedPartial_exp_formula
#print axioms remainder_nonneg
#print axioms mixedPartial_exp_ge_leading
end Legacy.BecknerOnofri.MixedExponentialDerivatives

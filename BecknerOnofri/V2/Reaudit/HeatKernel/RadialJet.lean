module

public import BecknerOnofri.V2.Reaudit.HeatKernel.MixedPartialSymmetry
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! # S014: the radial substitution `g_y(t) = f(t y)`

For `y ≥ 0` in `ℝ^d` and `f` smooth on the closed cube, the printed proof of
`lem:positive-bernstein` uses
`g_y^{(n)}(t) = ∑_{|α|=n} (n!/α!) y^α ∂^α f(t y)` (eq. `radial-absolute-monotonicity`).
Here this is proved in the form
* `g_y^{(n)}(t) = ((radialD y)^[n] f)(t y)` with `radialD y h = ∑_i y_i ∂_i h`
  (`iteratedDerivWithin_ray`);
* `(radialD y)^[n] f` has nonnegative values on the cube if all `∂^L f ≥ 0` there
  (`radialD_iterate_nonneg`);
* `((radialD y)^[n] f)(0) = ∑_{|α|=n} (n!/α!) y^α ∂^α f(0)` with `∂^α f(0)` the repository's
  `mixedPartial (directions α) f 0` (`radialD_iterate_zero`), via the multinomial theorem
  (`MvPolynomial.coeff_linearCombination_X_pow_of_fintype`) and the order independence of
  mixed partials on the cube (`mixedPartial_eq_of_directionIndex_eq`).
-/

noncomputable section
open Set Finset
open scoped ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri.FiniteDifferences

variable {d : ℕ}

/-- The radial derivative `∑_i y_i ∂_i`. -/
def radialD (y : Space d) (h : Space d → ℝ) : Space d → ℝ :=
  fun x => ∑ i, y i * coordinateDerivative i h x

theorem contDiffOn_radialD (y : Space d) {h : Space d → ℝ} (hh : ContDiffOn ℝ ∞ h (closedCube d)) :
    ContDiffOn ℝ ∞ (radialD y h) (closedCube d) := by
  unfold radialD
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.mul (contDiffOn_coordinateDerivative hh i)

theorem contDiffOn_radialD_iterate (y : Space d) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ ∞ h (closedCube d)) (n : ℕ) :
    ContDiffOn ℝ ∞ ((radialD y)^[n] h) (closedCube d) := by
  induction n generalizing h with
  | zero => exact hh
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (contDiffOn_radialD y hh)

theorem vec_eq_sum_basis (y : Space d) : y = ∑ i, y i • basis i := by
  ext j
  simp [basis, Pi.single_apply, Finset.sum_apply]

theorem hasDerivWithinAt_ray {H : Space d → ℝ} (hH : ContDiffOn ℝ ∞ H (closedCube d))
    (y : Space d) {R : ℝ} (hmaps : ∀ t ∈ Ico (0 : ℝ) R, t • y ∈ closedCube d) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) R) :
    HasDerivWithinAt (fun s : ℝ => H (s • y)) (radialD y H (t • y)) (Ico 0 R) t := by
  have hdiff : HasFDerivWithinAt H (fderivWithin ℝ H (closedCube d) (t • y)) (closedCube d)
      (t • y) := ((hH.differentiableOn (by simp)) _ (hmaps t ht)).hasFDerivWithinAt
  have hray : HasDerivWithinAt (fun s : ℝ => s • y) y (Ico 0 R) t := by
    have := ((hasDerivAt_id t).smul_const y).hasDerivWithinAt (s := Ico 0 R)
    simpa using this
  have hc := hdiff.comp_hasDerivWithinAt t hray (fun s hs => hmaps s hs)
  have e : (fderivWithin ℝ H (closedCube d) (t • y)) y = radialD y H (t • y) := by
    have e0 := congrArg (fderivWithin ℝ H (closedCube d) (t • y)) (vec_eq_sum_basis y)
    rw [e0]
    simp only [radialD, coordinateDerivative, map_sum, map_smul, smul_eq_mul]
  have hc' : HasDerivWithinAt (fun s : ℝ => H (s • y))
      ((fderivWithin ℝ H (closedCube d) (t • y)) y) (Ico 0 R) t := hc
  rwa [e] at hc'

theorem iteratedDerivWithin_ray {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (y : Space d) {R : ℝ} (hmaps : ∀ t ∈ Ico (0 : ℝ) R, t • y ∈ closedCube d) (n : ℕ) :
    ∀ t ∈ Ico (0 : ℝ) R,
      iteratedDerivWithin n (fun s : ℝ => f (s • y)) (Ico 0 R) t = ((radialD y)^[n] f) (t • y) := by
  induction n with
  | zero => intro t _; simp
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    have hH := contDiffOn_radialD_iterate y hf n
    have h1 : derivWithin (iteratedDerivWithin n (fun s : ℝ => f (s • y)) (Ico 0 R)) (Ico 0 R) t =
        derivWithin (fun s : ℝ => ((radialD y)^[n] f) (s • y)) (Ico 0 R) t :=
      derivWithin_congr (fun s hs => ih s hs) (ih t ht)
    rw [h1, (hasDerivWithinAt_ray hH y hmaps ht).derivWithin (uniqueDiffOn_Ico 0 R t ht),
      Function.iterate_succ_apply']

/-- The class of functions that are smooth on the cube with all iterated partials nonnegative. -/
def NonnegJet (f : Space d → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (closedCube d) ∧
    ∀ (L : List (Fin d)) (x : Space d), x ∈ closedCube d → 0 ≤ mixedPartial L f x

theorem NonnegJet.radialD {y : Space d} (hy : ∀ i, 0 ≤ y i) {h : Space d → ℝ}
    (hh : NonnegJet h) : NonnegJet (radialD y h) := by
  refine ⟨contDiffOn_radialD y hh.1, fun L x hx => ?_⟩
  have h1 : mixedPartial L (HeatKernel.radialD y h) x =
      ∑ i, y i * mixedPartial L (coordinateDerivative i h) x :=
    mixedPartial_sum L Finset.univ y (fun i => coordinateDerivative i h)
      (fun i => contDiffOn_coordinateDerivative hh.1 i) hx
  rw [h1]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hy i) (hh.2 (i :: L) x hx))

theorem NonnegJet.radialD_iterate {y : Space d} (hy : ∀ i, 0 ≤ y i) {h : Space d → ℝ}
    (hh : NonnegJet h) (n : ℕ) : NonnegJet ((HeatKernel.radialD y)^[n] h) := by
  induction n generalizing h with
  | zero => exact hh
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (hh.radialD hy)

end BecknerOnofri.V2.Reaudit.HeatKernel

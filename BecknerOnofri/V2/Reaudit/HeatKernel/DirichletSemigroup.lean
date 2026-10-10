module

public import BecknerOnofri.V2.Reaudit.HeatKernel.DirichletKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # The Dirichlet heat kernel is the kernel of the heat semigroup of `P_D` on `(0,1/2)`

With `φ_n = dirichletEig (n-1)` an orthonormal family of eigenfunctions (`integral_dirichletEig_mul`),
we show that the kernel defined by the eigenfunction expansion

* acts diagonally on the eigenbasis: `∫_0^{1/2} p_t^D(a,b) φ_m(b) db = e^{-(2π m)²t} φ_m(a)`;
* satisfies the semigroup law `p_{t+s}^D(a,b) = ∫_0^{1/2} p_t^D(a,c) p_s^D(c,b) dc`;
* is bounded by `4 ∑ e^{-λ_n t}`.

These facts say that `f ↦ ∫ p_t^D(·,b) f(b) db` is the heat semigroup `e^{-tP_D}` on the span of
the eigenfunctions, which is the content of "integral kernel of `e^{-tP_D}`" in the printed proof
of `prop:cosine-all` for a single interval factor.  (Completeness of the sine system in
`L²(0,1/2)` is not proved here.)
-/

noncomputable section
open Set Filter MeasureTheory intervalIntegral Topology
open scoped Real
namespace BecknerOnofri.V2.Reaudit.HeatKernel

theorem dirichletKernel_abs_le {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    |dirichletKernel t a b| ≤ ∑' n : ℕ, 4 * Real.exp (-dirichletEigval n * t) := by
  unfold dirichletKernel
  have hs := summable_dirichletKernel ht a b
  have hb : Summable (fun n : ℕ => 4 * Real.exp (-dirichletEigval n * t)) :=
    (summable_dirichlet_weights ht).mul_left 4
  calc |∑' n : ℕ, Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b|
      = ‖∑' n : ℕ, Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b‖ :=
        norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, 4 * Real.exp (-dirichletEigval n * t) :=
        Summable.tsum_le_tsum (fun n => by
          simpa only [Real.norm_eq_abs] using dirichletKernel_term_abs_le t n a b) hs.norm hb

/-- Termwise integration of the eigenfunction expansion against a bounded continuous function. -/
theorem integral_dirichletKernel_mul {t : ℝ} (ht : 0 < t) (a : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∫ b in (0 : ℝ)..(1 / 2), dirichletKernel t a b * g b =
      ∑' n : ℕ, Real.exp (-dirichletEigval n * t) * dirichletEig n a *
        ∫ b in (0 : ℝ)..(1 / 2), dirichletEig n b * g b := by
  have hcont : ∀ n : ℕ, Continuous (fun b : ℝ => dirichletEig n b) := by
    intro n; unfold dirichletEig; fun_prop
  have hD := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1 / 2)
    (F := fun (n : ℕ) (b : ℝ) =>
      Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b * g b)
    (f := fun b => dirichletKernel t a b * g b)
    (bound := fun n _ => 4 * M * Real.exp (-dirichletEigval n * t))
    (fun n => by
      apply Continuous.aestronglyMeasurable
      have := hcont n
      fun_prop)
    (fun n => Filter.Eventually.of_forall (fun b _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := dirichletEig_abs_le n a
      have h2 := dirichletEig_abs_le n b
      have h3 := hM b
      have h0 : 0 ≤ M := (abs_nonneg _).trans h3
      have h4 : |dirichletEig n a| * |dirichletEig n b| * |g b| ≤ 2 * 2 * M := by
        have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        nlinarith [abs_nonneg (dirichletEig n a), abs_nonneg (dirichletEig n b), abs_nonneg (g b)]
      have := Real.exp_pos (-dirichletEigval n * t)
      nlinarith))
    (Filter.Eventually.of_forall (fun b _ =>
      ((summable_dirichlet_weights ht).mul_left (4 * M))))
    (by
      apply Continuous.intervalIntegrable
      exact continuous_const)
    (Filter.Eventually.of_forall (fun b _ => by
      exact (summable_dirichletKernel ht a b).hasSum.mul_right (g b)))
  have e1 : ∀ n : ℕ, (∫ b in (0 : ℝ)..(1 / 2),
      Real.exp (-dirichletEigval n * t) * dirichletEig n a * dirichletEig n b * g b) =
      Real.exp (-dirichletEigval n * t) * dirichletEig n a *
        ∫ b in (0 : ℝ)..(1 / 2), dirichletEig n b * g b := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext b; ring
  simp_rw [e1] at hD
  exact hD.tsum_eq.symm

/-- The kernel acts diagonally on the eigenfunctions: `e^{-tP_D} φ_m = e^{-λ_m t} φ_m`. -/
theorem dirichletKernel_eigenaction {t : ℝ} (ht : 0 < t) (a : ℝ) (m : ℕ) :
    ∫ b in (0 : ℝ)..(1 / 2), dirichletKernel t a b * dirichletEig m b =
      Real.exp (-dirichletEigval m * t) * dirichletEig m a := by
  have hc : Continuous (fun b : ℝ => dirichletEig m b) := by unfold dirichletEig; fun_prop
  rw [integral_dirichletKernel_mul ht a hc (fun x => dirichletEig_abs_le m x)]
  rw [tsum_eq_single m]
  · rw [integral_dirichletEig_mul, if_pos rfl, mul_one]
  · intro n hn
    rw [integral_dirichletEig_mul, if_neg hn, mul_zero]

/-- **Semigroup law** (Chapman–Kolmogorov) for the Dirichlet heat kernel of `(0,1/2)`. -/
theorem dirichletKernel_semigroup {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (a b : ℝ) :
    ∫ c in (0 : ℝ)..(1 / 2), dirichletKernel t a c * dirichletKernel s c b =
      dirichletKernel (t + s) a b := by
  have hg : Continuous (fun c : ℝ => dirichletKernel s c b) := by
    have := (dirichletKernel_continuous hs).comp (continuous_id.prodMk continuous_const : Continuous
      (fun c : ℝ => (c, b)))
    exact this
  rw [integral_dirichletKernel_mul ht a hg (M := ∑' n : ℕ, 4 * Real.exp (-dirichletEigval n * s))
    (fun c => dirichletKernel_abs_le hs c b)]
  have hsum : dirichletKernel (t + s) a b = ∑' n : ℕ,
      Real.exp (-dirichletEigval n * (t + s)) * dirichletEig n a * dirichletEig n b := rfl
  rw [hsum]
  congr 1
  funext n
  have h1 : ∫ c in (0 : ℝ)..(1 / 2), dirichletEig n c * dirichletKernel s c b =
      Real.exp (-dirichletEigval n * s) * dirichletEig n b := by
    have : ∀ c : ℝ, dirichletEig n c * dirichletKernel s c b = dirichletKernel s b c * dirichletEig n c := by
      intro c
      rw [dirichletKernel_symm hs c b]; ring
    simp_rw [this]
    exact dirichletKernel_eigenaction hs b n
  rw [h1]
  have : Real.exp (-dirichletEigval n * (t + s)) =
      Real.exp (-dirichletEigval n * t) * Real.exp (-dirichletEigval n * s) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

end BecknerOnofri.V2.Reaudit.HeatKernel

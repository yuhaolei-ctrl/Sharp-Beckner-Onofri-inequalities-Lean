import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic

/-! Coefficient compactness and geometric majorants for positive multivariate
polynomials. The indices are Mathlib's actual multivariate-polynomial indices. -/

open scoped BigOperators Topology
open Filter

namespace Legacy.BecknerOnofri.PositivePolynomialLimit

set_option maxHeartbeats 600000

abbrev Index (d : ℕ) := Fin d →₀ ℕ
abbrev Cube (d : ℕ) := Fin d → unitInterval

noncomputable def monomialValue {d : ℕ} (a : Index d) (y : Cube d) : ℝ :=
  ∏ i, (y i : ℝ) ^ a i

theorem monomialValue_nonneg {d : ℕ} (a : Index d) (y : Cube d) :
    0 ≤ monomialValue a y :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (y i).property.1 _)

theorem monomialValue_le_one {d : ℕ} (a : Index d) (y : Cube d) :
    monomialValue a y ≤ 1 := by
  exact Finset.prod_le_one (fun i _ => pow_nonneg (y i).property.1 _)
    (fun i _ => pow_le_one₀ (y i).property.1 (y i).property.2)

theorem continuous_monomialValue {d : ℕ} (a : Index d) :
    Continuous (monomialValue a) := by
  unfold monomialValue
  fun_prop

theorem coefficient_summable {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    Summable (fun a : Index d => P.coeff a) := by
  exact summable_of_ne_finset_zero (fun a ha => MvPolynomial.notMem_support_iff.mp ha)

theorem polynomial_eval_eq_tsum {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (y : Cube d) :
    MvPolynomial.eval (fun i => (y i : ℝ)) P =
      ∑' a : Index d, P.coeff a * monomialValue a y := by
  rw [MvPolynomial.eval_eq']
  exact (tsum_eq_sum (s := P.support) (fun a ha => by
    rw [MvPolynomial.notMem_support_iff.mp ha, zero_mul])).symm

theorem coefficient_mass_eq_eval_one {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    (∑' a : Index d, P.coeff a) = MvPolynomial.eval (fun _ => (1:ℝ)) P := by
  simpa [monomialValue] using (polynomial_eval_eq_tsum P (fun _ => (1 : unitInterval))).symm

theorem coefficient_sum_le_mass {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : ∀ a, 0 ≤ P.coeff a) (s : Finset (Index d)) :
    ∑ a ∈ s, P.coeff a ≤ MvPolynomial.eval (fun _ => (1:ℝ)) P := by
  rw [← coefficient_mass_eq_eval_one]
  exact (coefficient_summable P).sum_le_tsum s (fun a _ => hP a)

theorem coefficient_le_mass {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : ∀ a, 0 ≤ P.coeff a) (a : Index d) :
    P.coeff a ≤ MvPolynomial.eval (fun _ => (1:ℝ)) P := by
  simpa using coefficient_sum_le_mass P hP {a}

theorem limit_coefficient_nonneg {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {c : Index d → ℝ}
    (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a))) (a : Index d) :
    0 ≤ c a :=
  ge_of_tendsto (hlim a) (Eventually.of_forall (fun m => hP m a))

theorem limit_coefficient_sum_le {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    (s : Finset (Index d)) : ∑ a ∈ s, c a ≤ M := by
  apply le_of_tendsto (tendsto_finsetSum s (fun a _ => hlim a))
  exact Eventually.of_forall (fun m => (coefficient_sum_le_mass (P m) (hP m) s).trans_eq (hmass m))

theorem limit_coefficient_summable {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a))) :
    Summable c :=
  summable_of_sum_le (limit_coefficient_nonneg hP hlim)
    (limit_coefficient_sum_le hP hmass hlim)

theorem geometric_product_summable (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun a : Fin d → ℕ => ∏ i, r ^ a i) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    have hg : Summable (fun n : ℕ => r^n) := summable_geometric_of_norm_lt_one
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    have hs := hg.mul_of_nonneg ih (fun n => pow_nonneg hr0 n)
      (fun a => Finset.prod_nonneg (fun i _ => pow_nonneg hr0 _))
    apply (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).summable_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv] using hs

theorem geometric_index_summable (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun a : Index d => ∏ i, r ^ a i) := by
  exact (Finsupp.equivFunOnFinite : Index d ≃ (Fin d → ℕ)).summable_iff.mpr
    (geometric_product_summable d hr0 hr1)

theorem monomialValue_le_geometric {d : ℕ} (a : Index d) (y : Cube d)
    {r : ℝ} (hyr : ∀ i, (y i : ℝ) ≤ r) : monomialValue a y ≤ ∏ i, r ^ a i := by
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (y i).property.1 _)
    (fun i _ => pow_le_pow_left₀ (y i).property.1 (hyr i) _)

end Legacy.BecknerOnofri.PositivePolynomialLimit

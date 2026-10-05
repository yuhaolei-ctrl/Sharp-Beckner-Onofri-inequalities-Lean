module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

@[expose] public section

/-! Actual tensor Bernstein polynomials on the closed finite-dimensional cube. -/
noncomputable section
open Finset Filter
open scoped BigOperators Topology unitInterval
namespace Legacy.BecknerOnofri.TensorBernstein

abbrev Cube (d : ℕ) := Fin d → unitInterval
abbrev Grid (d m : ℕ) := Fin d → Fin (m+1)

def point {d m : ℕ} (j : Grid d m) : Cube d := fun i => bernstein.z (j i)
def weight {d : ℕ} (m : ℕ) (j : Grid d m) (y : Cube d) : ℝ :=
  ∏ i, bernstein m (j i) (y i)
def approx {d : ℕ} (m : ℕ) (f : Cube d → ℝ) (y : Cube d) : ℝ :=
  ∑ j : Grid d m, f (point j) * weight m j y

theorem weight_nonneg {d m : ℕ} (j : Grid d m) (y : Cube d) : 0 ≤ weight m j y :=
  prod_nonneg (fun _ _ => bernstein_nonneg)

theorem sum_weight {d : ℕ} (m : ℕ) (y : Cube d) : ∑ j : Grid d m, weight m j y = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun (i : Fin d) (k : Fin (m+1)) => bernstein m k (y i))]
  simp

private theorem coordinate_moment {d m : ℕ} (i : Fin d) (a : Fin (m+1) → ℝ) (y : Cube d) :
    (∑ j : Grid d m, a (j i) * weight m j y) =
      ∑ k : Fin (m+1), a k * bernstein m k (y i) := by
  have hp (j : Grid d m) : a (j i) * weight m j y =
      ∏ l : Fin d, ((if l = i then a (j l) else 1) * bernstein m (j l) (y l)) := by
    rw [prod_mul_distrib]
    simp [weight]
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun (l : Fin d) (k : Fin (m+1)) =>
    (if l = i then a k else 1) * bernstein m k (y l))]
  have hf (l : Fin d) : (∑ k : Fin (m+1),
      (if l = i then a k else 1) * bernstein m k (y l)) =
      if l = i then ∑ k : Fin (m+1), a k * bernstein m k (y i) else 1 := by
    by_cases h : l = i
    · subst l; simp
    · simp [h]
  simp_rw [hf]
  simp

def squaredDistance {d : ℕ} (x y : Cube d) : ℝ :=
  ∑ i, ((x i:ℝ)-(y i:ℝ))^2

theorem squaredDistance_nonneg {d : ℕ} (x y : Cube d) : 0 ≤ squaredDistance x y :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem total_variance {d m : ℕ} (hm : m ≠ 0) (y : Cube d) :
    (∑ j : Grid d m, squaredDistance y (point j) * weight m j y) =
      ∑ i, (y i:ℝ)*(1-(y i:ℝ))/(m:ℝ) := by
  unfold squaredDistance
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  change (∑ j : Grid d m, ((y i:ℝ)-(bernstein.z (j i):ℝ))^2 * weight m j y) = _
  rw [coordinate_moment i (fun k => ((y i:ℝ)-(bernstein.z k:ℝ))^2) y]
  exact bernstein.variance hm (y i)

theorem total_variance_le {d m : ℕ} (hm : m ≠ 0) (y : Cube d) :
    (∑ j : Grid d m, squaredDistance y (point j) * weight m j y) ≤ (d:ℝ)/(m:ℝ) := by
  rw [total_variance hm]
  calc
    _ ≤ ∑ _i : Fin d, 1/(m:ℝ) := by
      apply sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
      have hy0 := (y i).property.1
      have hy1 := (y i).property.2
      nlinarith
    _ = _ := by simp [div_eq_mul_inv]

/-- A coordinate witnesses failure of closeness in the finite product metric. -/
theorem squaredDistance_ge_of_dist_ge {d : ℕ} (x y : Cube d) {delta : ℝ}
    (hd : 0 < delta) (hxy : delta ≤ dist x y) : delta^2 ≤ squaredDistance x y := by
  have hn : ¬ ∀ i, dist (x i) (y i) < delta := by
    intro h
    exact (not_lt_of_ge hxy) ((dist_pi_lt_iff hd).2 h)
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  have hsq : delta^2 ≤ ((x i:ℝ)-(y i:ℝ))^2 := by
    have hdist : dist (x i) (y i) = |(x i:ℝ)-(y i:ℝ)| := rfl
    rw [hdist] at hi
    nlinarith [sq_abs ((x i:ℝ)-(y i:ℝ))]
  apply hsq.trans
  change ((x i:ℝ)-(y i:ℝ))^2 ≤ ∑ l, ((x l:ℝ)-(y l:ℝ))^2
  exact single_le_sum (fun l _ => sq_nonneg ((x l:ℝ)-(y l:ℝ))) (mem_univ i)

/-- A quantitative uniform estimate using the sum of the coordinate variances. -/
theorem error_le {d m : ℕ} (hm : m ≠ 0) (f : Cube d → ℝ)
    {C delta e : ℝ} (hC : 0 ≤ C) (hd : 0 < delta) (he : 0 ≤ e)
    (hbound : ∀ x y, ‖f x-f y‖ ≤ C)
    (hlocal : ∀ x y, dist x y < delta → ‖f x-f y‖ ≤ e) (y : Cube d) :
    ‖approx m f y-f y‖ ≤ e + C/delta^2 * ((d:ℝ)/(m:ℝ)) := by
  have hc : 0 ≤ C/delta^2 := div_nonneg hC (sq_nonneg _)
  have hpoint (j : Grid d m) : ‖f (point j)-f y‖ ≤
      e + C/delta^2 * squaredDistance y (point j) := by
    by_cases h : dist (point j) y < delta
    · exact (hlocal _ _ h).trans (le_add_of_nonneg_right
        (mul_nonneg hc (squaredDistance_nonneg _ _)))
    · have hD := squaredDistance_ge_of_dist_ge y (point j) hd
        (by simpa only [dist_comm] using le_of_not_gt h)
      have hC' : C ≤ C/delta^2 * squaredDistance y (point j) := by
        calc
          C = C/delta^2 * delta^2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hD hc
      exact (hbound _ _).trans (hC'.trans (le_add_of_nonneg_left he))
  have heq : approx m f y-f y =
      ∑ j : Grid d m, weight m j y * (f (point j)-f y) := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_weight, one_mul]
    unfold approx
    rw [sum_congr rfl (fun j _ => mul_comm (weight m j y) (f (point j)))]
  rw [heq]
  calc
    _ ≤ ∑ j : Grid d m, ‖weight m j y * (f (point j)-f y)‖ := norm_sum_le _ _
    _ = ∑ j : Grid d m, weight m j y * ‖f (point j)-f y‖ := by
      simp_rw [norm_mul, Real.norm_of_nonneg (weight_nonneg _ _)]
    _ ≤ ∑ j : Grid d m, weight m j y *
        (e+C/delta^2*squaredDistance y (point j)) :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (weight_nonneg _ _))
    _ = e+C/delta^2 * ∑ j : Grid d m, squaredDistance y (point j) * weight m j y := by
      simp_rw [mul_add, sum_add_distrib, ← sum_mul]
      rw [sum_weight, one_mul, mul_sum]
      congr 1
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (total_variance_le hm y) hc)

/-- The concrete tensor Bernstein approximation converges uniformly on the closed cube. -/
theorem uniform {d : ℕ} (f : Cube d → ℝ) (hf : Continuous f) :
    TendstoUniformly (fun m => approx m f) f atTop := by
  have hcont : Continuous (fun p : Cube d × Cube d => f p.1-f p.2) :=
    (hf.comp continuous_fst).sub (hf.comp continuous_snd)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hbound (x y : Cube d) : ‖f x-f y‖ ≤ C := hC (x,y) (Set.mem_univ _)
  have hC0 : 0 ≤ C := by simpa using hbound (fun _ => 0) (fun _ => 0)
  have huc := CompactSpace.uniformContinuous_of_continuous hf
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  obtain ⟨delta, hd, hdelta⟩ := Metric.uniformContinuous_iff.mp huc (e/2) (by linarith)
  have ht := tendsto_const_div_atTop_nhds_zero_nat (C/delta^2*(d:ℝ))
  filter_upwards [ht.eventually_lt_const (by linarith : (0:ℝ) < e/2),
    eventually_ne_atTop 0] with m hm hmn
  intro y
  have hb := error_le hmn f hC0 hd (by linarith : (0:ℝ) ≤ e/2) hbound
    (fun x y hxy => by simpa only [dist_eq_norm] using (hdelta hxy).le) y
  rw [dist_comm, dist_eq_norm]
  have heq : C/delta^2*((d:ℝ)/(m:ℝ)) = (C/delta^2*(d:ℝ))/(m:ℝ) := by ring
  rw [heq] at hb
  linarith

/-- The actual multivariate polynomial, with real coefficients sampled on the grid. -/
def polynomial {d : ℕ} (m : ℕ) (f : Cube d → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ j : Grid d m, MvPolynomial.C (f (point j)) *
    ∏ i : Fin d, (MvPolynomial.C ((m.choose (j i):ℝ)) * MvPolynomial.X i ^ (j i).val *
      (1-MvPolynomial.X i)^(m-(j i).val))

theorem polynomial_eval {d : ℕ} (m : ℕ) (f : Cube d → ℝ) (y : Cube d) :
    MvPolynomial.eval (fun i => (y i:ℝ)) (polynomial m f) = approx m f y := by
  simp [polynomial, approx, weight, bernstein_apply]

theorem approx_formula {d : ℕ} (m : ℕ) (f : Cube d → ℝ) (y : Cube d) :
    approx m f y = ∑ j : Grid d m,
      f (fun i => bernstein.z (j i)) *
        ∏ i, (m.choose (j i):ℝ)*(y i:ℝ)^(j i).val*(1-(y i:ℝ))^(m-(j i).val) := by
  simp only [approx, weight, bernstein_apply]
  rfl

/-- Positive-degree tensor Bernstein polynomials reproduce the corner value exactly. -/
theorem approx_one {d m : ℕ} (hm : m ≠ 0) (f : Cube d → ℝ) :
    approx m f (fun _ => 1) = f (fun _ => 1) := by
  have hb (k : Fin (m+1)) (hk : k ≠ Fin.last m) : bernstein m k 1 = 0 := by
    have hlt : k.val < m := by
      have he : k.val ≠ m := fun h => hk (Fin.ext h)
      omega
    simp [bernstein_apply, Nat.sub_pos_of_lt hlt |>.ne']
  unfold approx
  rw [sum_eq_single (fun _ : Fin d => Fin.last m)]
  · simp [weight, bernstein_apply]
    congr 1
    funext i
    exact bernstein.z_last hm
  · intro j hj hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hz : weight m j (fun _ : Fin d => 1) = 0 :=
      prod_eq_zero (mem_univ i) (hb (j i) hi)
    rw [hz, mul_zero]
  · simp

theorem polynomial_eval_one {d m : ℕ} (hm : m ≠ 0) (f : Cube d → ℝ) :
    MvPolynomial.eval (fun _ : Fin d => (1:ℝ)) (polynomial m f) = f (fun _ => 1) := by
  exact (polynomial_eval m f (fun _ => 1)).trans (approx_one hm f)

/-- Continuous-map form of the same concrete tensor approximation theorem. -/
theorem continuousMap_uniform {d : ℕ} (f : C(Cube d, ℝ)) :
    TendstoUniformly (fun m => approx m f) f atTop := uniform f f.continuous

/-- Positive-degree indexing gives the fixed corner mass needed by coefficient limits. -/
theorem polynomial_succ_uniform {d : ℕ} (f : Cube d → ℝ) (hf : Continuous f) :
    TendstoUniformly (fun m y =>
      MvPolynomial.eval (fun i => (y i:ℝ)) (polynomial (m+1) f)) f atTop := by
  simp_rw [polynomial_eval]
  intro v hv
  exact (tendsto_add_atTop_nat 1).eventually ((uniform f hf) v hv)

#print axioms uniform
#print axioms polynomial_eval
#print axioms polynomial_eval_one
#print axioms polynomial_succ_uniform
end Legacy.BecknerOnofri.TensorBernstein

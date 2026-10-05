module

public import Legacy.BecknerOnofri.PositivePolynomialLimitCore

@[expose] public section

/-! The second half of the positive Bernstein/Taylor argument. Nonnegative
polynomial coefficients with a common mass and coefficientwise limits give
an exact positive power series for a continuous pointwise polynomial limit.
No power-series identity or equality of limiting coefficient mass is assumed. -/

open scoped BigOperators Topology
open Filter

namespace Legacy.BecknerOnofri.PositivePolynomialLimit

set_option maxHeartbeats 600000

theorem series_term_norm_le {d : ℕ} {c : Index d → ℝ} (hc : ∀ a, 0 ≤ c a)
    (a : Index d) (y : Cube d) : ‖c a * monomialValue a y‖ ≤ c a := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc a) (monomialValue_nonneg a y))]
  exact mul_le_of_le_one_right (hc a) (monomialValue_le_one a y)

theorem series_summable {d : ℕ} {c : Index d → ℝ} (hc : ∀ a, 0 ≤ c a)
    (hs : Summable c) (y : Cube d) : Summable (fun a => c a * monomialValue a y) :=
  hs.of_norm_bounded (fun a => series_term_norm_le hc a y)

theorem series_continuous {d : ℕ} {c : Index d → ℝ} (hc : ∀ a, 0 ≤ c a)
    (hs : Summable c) : Continuous (fun y : Cube d => ∑' a, c a * monomialValue a y) :=
  continuous_tsum (fun a => continuous_const.mul (continuous_monomialValue a)) hs
    (series_term_norm_le hc)

theorem series_uniform {d : ℕ} {c : Index d → ℝ} (hc : ∀ a, 0 ≤ c a)
    (hs : Summable c) :
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, c a * monomialValue a y) (fun y => ∑' a, c a * monomialValue a y) atTop :=
  tendstoUniformly_tsum hs (series_term_norm_le hc)

theorem interior_representation {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ}
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i:ℝ)) (P m)) atTop (𝓝 (f y)))
    (y : Cube d) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hyr : ∀ i, (y i:ℝ) ≤ r) :
    f y = ∑' a, c a * monomialValue a y := by
  have hM : 0 ≤ M := by
    have h := (coefficient_sum_le_mass (P 0) (hP 0) ∅).trans_eq (hmass 0)
    simpa using h
  have ht := tendsto_tsum_of_dominated_convergence
    ((geometric_index_summable d hr0 hr1).mul_left M)
    (fun a => (hlim a).mul_const (monomialValue a y))
    (Eventually.of_forall (fun m a => ?_))
  · have hpoly : Tendsto (fun m => ∑' a, (P m).coeff a * monomialValue a y)
        atTop (𝓝 (f y)) := by
      simpa only [← polynomial_eval_eq_tsum] using hf y
    exact tendsto_nhds_unique hpoly ht
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hP m a) (monomialValue_nonneg a y))]
    exact mul_le_mul ((coefficient_le_mass (P m) (hP m) a).trans_eq (hmass m))
      (monomialValue_le_geometric a y hyr) (monomialValue_nonneg a y) hM

noncomputable def shrinkScale (m : ℕ) : unitInterval :=
  ⟨1 - 1/((m:ℝ)+2), by
    have hd : (0:ℝ) < (m:ℝ)+2 := by positivity
    have hi : 1/((m:ℝ)+2) ≤ 1 := (div_le_one hd).mpr (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
    constructor
    · linarith
    · have : 0 ≤ 1/((m:ℝ)+2) := by positivity
      linarith⟩

theorem shrinkScale_lt_one (m : ℕ) : (shrinkScale m : ℝ) < 1 := by
  change 1 - 1/((m:ℝ)+2) < 1
  have : 0 < 1/((m:ℝ)+2) := by positivity
  linarith

theorem shrinkScale_tendsto : Tendsto (fun m => (shrinkScale m : ℝ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop :=
    Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp ht
  simpa [shrinkScale, div_eq_mul_inv] using tendsto_const_nhds.sub hi

noncomputable def shrink {d : ℕ} (m : ℕ) (y : Cube d) : Cube d :=
  fun i => shrinkScale m * y i

theorem shrink_le_scale {d : ℕ} (m : ℕ) (y : Cube d) (i : Fin d) :
    (shrink m y i : ℝ) ≤ (shrinkScale m : ℝ) := unitInterval.mul_le_left

theorem shrink_tendsto {d : ℕ} (y : Cube d) : Tendsto (fun m => shrink m y) atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_subtype_rng.mpr
  simpa [shrink] using shrinkScale_tendsto.mul_const (y i : ℝ)

/-- Equality on all faces follows from continuity and the positive-series
M-test, after the interior identity has been proved by dominated convergence. -/
theorem representation {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i:ℝ)) (P m)) atTop (𝓝 (f y)))
    (y : Cube d) : f y = ∑' a, c a * monomialValue a y := by
  have hc := limit_coefficient_nonneg hP hlim
  have hs := limit_coefficient_summable hP hmass hlim
  have hl := hfc.continuousAt.tendsto.comp (shrink_tendsto y)
  have hr := (series_continuous hc hs).continuousAt.tendsto.comp (shrink_tendsto y)
  have he (m : ℕ) : f (shrink m y) = ∑' a, c a * monomialValue a (shrink m y) :=
    interior_representation hP hmass hlim hf _ (shrinkScale m).property.1
      (shrinkScale_lt_one m) (shrink_le_scale m y)
  exact tendsto_nhds_unique hl (by simpa only [Function.comp_def, he] using hr)

/-- The representation includes actual convergence, rather than a totalized
sum that could take its default value for a nonsummable series. -/
theorem hasSum_representation {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i:ℝ)) (P m)) atTop (𝓝 (f y)))
    (y : Cube d) : HasSum (fun a => c a * monomialValue a y) (f y) := by
  rw [representation hP hmass hlim hfc hf y]
  exact (series_summable (limit_coefficient_nonneg hP hlim)
    (limit_coefficient_summable hP hmass hlim) y).hasSum

/-- No coefficient mass escapes to infinite degree. This is a conclusion,
obtained by evaluating the established closed-cube identity at the corner. -/
theorem coefficient_hasSum_mass {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i:ℝ)) (P m)) atTop (𝓝 (f y))) :
    HasSum c M := by
  have hconst : Tendsto (fun m => MvPolynomial.eval (fun _ : Fin d => (1:ℝ)) (P m))
      atTop (𝓝 M) := by simpa only [hmass] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (𝓝 M))
  have hcorner : f (fun _ => 1) = M :=
    tendsto_nhds_unique (hf (fun _ => 1)) (by simpa using hconst)
  have he := representation hP hmass hlim hfc hf (fun _ => 1)
  simp [monomialValue] at he
  have hs := (limit_coefficient_summable hP hmass hlim).hasSum
  rw [← he, hcorner] at hs
  exact hs

/-- Uniform convergence on the entire closed cube of the limiting positive
monomial series. The approximating polynomials need only converge pointwise. -/
theorem uniform_representation {d : ℕ} {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1:ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i:ℝ)) (P m)) atTop (𝓝 (f y))) :
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, c a * monomialValue a y) f atTop := by
  have he : f = (fun y => ∑' a, c a * monomialValue a y) :=
    funext (representation hP hmass hlim hfc hf)
  rw [he]
  exact series_uniform (limit_coefficient_nonneg hP hlim) (limit_coefficient_summable hP hmass hlim)

#print axioms representation
#print axioms hasSum_representation
#print axioms coefficient_hasSum_mass
#print axioms uniform_representation
end Legacy.BecknerOnofri.PositivePolynomialLimit

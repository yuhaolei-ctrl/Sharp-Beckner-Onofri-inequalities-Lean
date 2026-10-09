module

public import BecknerOnofri.V2.Assembly.Hypotheses
public import BecknerOnofri.V2.Assembly.LargeMean
public import BecknerOnofri.V2.FiniteState.EntropyConvexity
public import BecknerOnofri.V2.FiniteState.OriginOrthogonality
public import BecknerOnofri.V2.FiniteState.FamilyVariance
public import BecknerOnofri.V2.Circle.Psi

@[expose] public section

/-!
# Proposition 5.12(ii) in count form (work package G14)

Source: "Completion of the proof of Proposition 5.12(ii)" together with Lemma 5.19/5.20/5.21 and the
large-mean paragraph.  For every `t ∈ [0,1]` and every `q ∈ 𝒫_t` (the whole feasible set, NOT only the
reference family `p(t)`; zero coordinates allowed):

* `0 ≤ t ≤ 99/100`: variance comparison (`family_variance_comparison`) with the three scalar bounds
  (`ScalarBounds`) gives `F(q) + 12 ψ(t) ≥ (1/10 - (30/7)(1/50)) t⁴ = t⁴/70` (strict for `t > 0`);
* `t = 0` additionally: Corollary 5.18 at `p = b` retains `F(q) ≥ Hr(q|b)/5 ≥ 0`, and equality forces
  `q = b` (`functional_zero_mean`), and `F(b) = 0`;
* `99/100 ≤ t ≤ 1`: the coarse entropy/energy estimate (`large_mean_bound`), margin `3/100 > 1/70`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open scoped BigOperators
namespace BecknerOnofri.V2.Assembly
open BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-! ### Relative entropy: nonnegativity and rigidity -/

theorem entropy_term_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    0 ≤ x * Real.log (x / y) - (x - y) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp [hy.le]
  · have hr : 0 < y / x := div_pos hy h
    have hl := Real.log_le_sub_one_of_pos hr
    have e : Real.log (x / y) = - Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    rw [e]
    have : x * (y / x - 1) = y - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hl h.le]

theorem entropy_term_eq_zero {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    (h : x * Real.log (x / y) - (x - y) = 0) : x = y := by
  rcases hx.eq_or_lt with h0 | h0
  · subst h0
    simp at h
    linarith
  · by_contra hne
    have hr : 0 < y / x := div_pos hy h0
    have hr1 : y / x ≠ 1 := by
      intro h1
      apply hne
      field_simp at h1
      linarith
    have hl := Real.log_lt_sub_one_of_pos hr hr1
    have e : Real.log (x / y) = - Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    rw [e] at h
    have : x * (y / x - 1) = y - x := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hl h0]

theorem relativeEntropy_split {p q : Count → ℝ} (hpm : (∑ j : Count, p j) = 1)
    (hqm : (∑ j : Count, q j) = 1) :
    relativeEntropy q p =
      ∑ j : Count, (q j * Real.log (q j / p j) - (q j - p j)) := by
  unfold relativeEntropy
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hpm, hqm]
  ring

theorem relativeEntropy_nonneg_of_mass {p q : Count → ℝ} (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 ≤ q j)
    (hpm : (∑ j : Count, p j) = 1) (hqm : (∑ j : Count, q j) = 1) : 0 ≤ relativeEntropy q p := by
  rw [relativeEntropy_split hpm hqm]
  exact Finset.sum_nonneg (fun j _ => entropy_term_nonneg (hq j) (hp j))

theorem eq_of_relativeEntropy_eq_zero {p q : Count → ℝ} (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 ≤ q j)
    (hpm : (∑ j : Count, p j) = 1) (hqm : (∑ j : Count, q j) = 1)
    (h : relativeEntropy q p = 0) : q = p := by
  rw [relativeEntropy_split hpm hqm] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => entropy_term_nonneg (hq j) (hp j))).mp h
  funext j
  exact entropy_term_eq_zero (hq j) (hp j) (h0 j (Finset.mem_univ j))

/-! ### The fair binomial reference: `W b = 0`, `F(b) = 0`, `g_j(b) = 2` -/

theorem sum_interaction_reference (j : Count) :
    (∑ k : Count, interaction j k * reference k) = 0 := by
  simp_rw [interaction_eq]
  have : ∀ k : Count, (∑ s : Order, weight s * moment s j * moment s k) * reference k =
      ∑ s : Order, weight s * moment s j * (reference k * moment s k) := by
    intro k
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s _
  rw [← Finset.mul_sum, reference_moment_zero, mul_zero]

theorem gradient_reference (j : Count) : gradient reference j = 2 := by
  unfold gradient
  rw [div_self (reference_pos j).ne', Real.log_one, sum_interaction_reference]
  ring

theorem quadratic_reference : quadratic reference = 0 := by
  rw [quadratic_eq_sum]
  apply Finset.sum_eq_zero
  intro s _
  have : (∑ j : Count, moment s j * reference j) = 0 := by
    simp_rw [mul_comm (moment s _) (reference _)]
    exact reference_moment_zero s
  rw [this]
  ring

theorem relativeEntropy_reference_self : relativeEntropy reference reference = 0 := by
  unfold relativeEntropy
  apply Finset.sum_eq_zero
  intro j _
  rw [div_self (reference_pos j).ne', Real.log_one, mul_zero]

theorem functional_reference : functional reference = 0 := by
  unfold functional
  rw [relativeEntropy_reference_self, quadratic_reference]
  ring

/-- **The case `t = 0`** (Corollary 5.18 with `p = b`): for every `q ∈ 𝒫_0`,
`F(q) ≥ Hr(q|b)/5 ≥ 0`, equality in `F(q) = 0` forces `q = b`; and `F(b) = 0`. -/
theorem functional_zero_mean {q : Count → ℝ} (hq : FeasibleAt 0 q) :
    relativeEntropy q reference / 5 ≤ functional q ∧ 0 ≤ functional q ∧
      (functional q = 0 → q = reference) := by
  have hcor := fixed_mean_entropy_convexity_affine reference_feasible reference_pos hq.1
    (by rw [reference_mean, hq.2])
  simp_rw [gradient_reference] at hcor
  rw [functional_reference, ← Finset.mul_sum, Finset.sum_sub_distrib, hq.1.2.1, reference_mass] at hcor
  simp only [sub_self, mul_zero, zero_add] at hcor
  have hre0 : 0 ≤ relativeEntropy q reference :=
    relativeEntropy_nonneg_of_mass reference_pos hq.1.1 reference_mass hq.1.2.1
  refine ⟨hcor, by linarith, fun hF => ?_⟩
  have : relativeEntropy q reference = 0 := by linarith
  exact eq_of_relativeEntropy_eq_zero reference_pos hq.1.1 reference_mass hq.1.2.1 this

/-! ### Assembly of Proposition 5.12(ii), count form -/

theorem psiV2_zero : psiV2 0 = 0 := by simp [psiV2]

/-- The variance-comparison step for `0 < t ≤ 99/100` (strict). -/
theorem count_form_mid (hsc : ScalarBounds) {t : ℝ} (ht0 : 0 < t) (h99 : t ≤ 99 / 100)
    {q : Count → ℝ} (hq : FeasibleAt t q) : t ^ 4 / 70 < functional q + 12 * psiV2 t := by
  obtain ⟨⟨hf, hfs⟩, hv, he⟩ := hsc t ht0.le h99
  have hcmp := family_variance_comparison ht0.le (by linarith) hq he
  have hfs' := hfs ht0
  linarith

/-- **Proposition 5.12(ii), count form, with the internal constant `1/70`.**  For `t ∈ [0,1]` and
every `q ∈ 𝒫_t`: `F(q) + 12 ψ(t) ≥ t⁴/70`. -/
theorem count_form_internal (hsc : ScalarBounds) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {q : Count → ℝ} (hq : FeasibleAt t q) : t ^ 4 / 70 ≤ functional q + 12 * psiV2 t := by
  rcases ht0.eq_or_lt with h0 | h0
  · subst h0
    have := (functional_zero_mean hq).2.1
    rw [psiV2_zero]
    norm_num
    linarith
  · by_cases h99 : t ≤ 99 / 100
    · exact (count_form_mid hsc h0 h99 hq).le
    · have hlt := large_mean_bound (not_le.mp h99).le ht1 hq
      have : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
      linarith

/-- **Proposition 5.12(ii), count form, public constant `1/250`** (the hypothesis `hcount` of
`Channel.spin_final_of_count_form`). -/
theorem count_form_public (hsc : ScalarBounds) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ p : Count → ℝ, FeasibleAt t p →
      t ^ 4 / 250 ≤ functional p + 12 * BecknerOnofri.V2.Circle.psi t := by
  intro t ht p hp
  have h := count_form_internal hsc ht.1 ht.2 hp
  have h4 : 0 ≤ t ^ 4 := by positivity
  have : BecknerOnofri.V2.Circle.psi t = psiV2 t := rfl
  rw [this]
  linarith

end BecknerOnofri.V2.Assembly

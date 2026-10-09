module

public import BecknerOnofri.V2.FiniteState.FamilyJets
public import BecknerOnofri.V2.FiniteState.FamilyBeta

@[expose] public section

/-!
# Explicit family near zero: exact mass and mean identities on a punctured neighbourhood

For the origin expansions one needs the exact identities `∑ p_j = 1` and `∑ x_j p_j = t` for all
`t` in a two-sided neighbourhood of `0` (negative `t` included), since big-O statements at `0`
are two-sided.  For small `t ≠ 0` one has `ω(t) > 0` and `|a(t)| < 1`, and the rational
product form is a genuine beta-binomial law with parameters `α = (1+a)/(2ω)`, `β = (1-a)/(2ω)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Rational product form of the beta-binomial component, for arbitrary `a, ω`. -/
def nuForm (a ω : ℝ) (j : Count) : ℝ :=
  ((12 : ℕ).choose j.val : ℝ) *
    (∏ k ∈ Finset.range j.val, ((1 + a) / 2 + (k : ℝ) * ω)) *
    (∏ k ∈ Finset.range (12 - j.val), ((1 - a) / 2 + (k : ℝ) * ω)) /
    (∏ k ∈ Finset.range 12, (1 + (k : ℝ) * ω))

theorem famNu_eq_nuForm (t : ℝ) (j : Count) : famNu t j = nuForm (famBias t) (famOmega t) j := rfl

theorem risingProd_div (x ω : ℝ) (hω : 0 < ω) (n : ℕ) :
    risingProd (x / ω) n = (ω⁻¹) ^ n * ∏ k ∈ Finset.range n, (x + (k : ℝ) * ω) := by
  unfold risingProd
  rw [← prod_range_const_mul]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  field_simp

theorem nuForm_eq_betaBinom {a ω : ℝ} (hω : 0 < ω) (j : Count) :
    nuForm a ω j = betaBinom ((1 + a) / 2 / ω) ((1 - a) / 2 / ω) j.val := by
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have hsum : (1 + a) / 2 / ω + (1 - a) / 2 / ω = 1 / ω := by field_simp; ring
  have hD : risingProd (1 / ω) 12 = (ω⁻¹) ^ 12 * ∏ k ∈ Finset.range 12, (1 + (k : ℝ) * ω) :=
    risingProd_div 1 ω hω 12
  unfold nuForm betaBinom
  rw [hsum, hD, risingProd_div _ ω hω, risingProd_div _ ω hω]
  have hpow : (ω⁻¹) ^ j.val * (ω⁻¹) ^ (12 - j.val) = (ω⁻¹) ^ 12 := by
    rw [← pow_add]; congr 1; omega
  have hne : (ω⁻¹) ^ 12 ≠ 0 := by positivity
  have key : ∀ (C P Q R w1 w2 w3 : ℝ), w1 * w2 = w3 → w3 ≠ 0 →
      C * P * Q / R = C * (w1 * P) * (w2 * Q) / (w3 * R) := by
    intro C P Q R w1 w2 w3 hw hw3
    have : C * (w1 * P) * (w2 * Q) = w3 * (C * P * Q) := by rw [← hw]; ring
    rw [this, mul_div_mul_left _ _ hw3]
  exact key _ _ _ _ _ _ _ hpow hne

theorem nuForm_sum {a ω : ℝ} (hω : 0 < ω) (ha0 : -1 < a) (ha1 : a < 1) :
    ∑ j : Count, nuForm a ω j = 1 := by
  have h1 : 0 < (1 + a) / 2 / ω := by apply div_pos <;> linarith
  have h2 : 0 < (1 - a) / 2 / ω := by apply div_pos <;> linarith
  simp_rw [nuForm_eq_betaBinom hω]
  rw [Fin.sum_univ_eq_sum_range (fun j => betaBinom ((1 + a) / 2 / ω) ((1 - a) / 2 / ω) j) 13]
  exact betaBinom_sum_beta h1 h2

theorem nuForm_mean {a ω : ℝ} (hω : 0 < ω) (ha0 : -1 < a) (ha1 : a < 1) :
    ∑ j : Count, meanCoordinate j * nuForm a ω j = a := by
  have h1 : 0 < (1 + a) / 2 / ω := by apply div_pos <;> linarith
  have h2 : 0 < (1 - a) / 2 / ω := by apply div_pos <;> linarith
  have hb1 := betaBinom_first_beta h1 h2
  have hb0 := betaBinom_sum_beta h1 h2
  have hsum : (1 + a) / 2 / ω + (1 - a) / 2 / ω = 1 / ω := by field_simp; ring
  have e : ∀ j : Count, meanCoordinate j * nuForm a ω j =
      (1 / 6) * ((j.val : ℝ) * betaBinom ((1 + a) / 2 / ω) ((1 - a) / 2 / ω) j.val) -
        betaBinom ((1 + a) / 2 / ω) ((1 - a) / 2 / ω) j.val := by
    intro j
    rw [nuForm_eq_betaBinom hω, meanCoordinate_eq_real]
    ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun j => (j : ℝ) * betaBinom ((1 + a) / 2 / ω) ((1 - a) / 2 / ω) j) 13,
    Fin.sum_univ_eq_sum_range (fun j => betaBinom ((1 + a) / 2 / ω) ((1 - a) / 2 / ω) j) 13,
    hb1, hb0, hsum]
  field_simp
  ring

theorem famL_nonneg_all (t : ℝ) : 0 ≤ famL t := by unfold famL; positivity

theorem famLam_bias_all (t : ℝ) : (1 - famLam t) * famBias t + famLam t = t := by
  have := famL_nonneg_all t
  unfold famLam famBias
  field_simp
  ring

/-- For small `t ≠ 0` (both signs) the family is a genuine beta-binomial mixture. -/
theorem eventually_famNear :
    ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 → 0 < famOmega t ∧ -1 < famBias t ∧ famBias t < 1 := by
  have hD : Continuous famOmegaDen := by unfold famOmegaDen famP; fun_prop
  have hDpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < famOmegaDen t := by
    have := hD.tendsto 0
    rw [famOmegaDen_zero] at this
    exact this.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 31))
  have hbias : Continuous famBias := by unfold famBias famL; fun_prop
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), famBias t < 1 := by
    have := hbias.tendsto 0
    rw [famBias_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), -1 < famBias t := by
    have := hbias.tendsto 0
    rw [famBias_zero] at this
    exact this.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  have h3 : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := gt_mem_nhds (by norm_num)
  filter_upwards [hDpos, h1, h2, h3] with t hD0 hb1 hb2 ht1 ht
  refine ⟨?_, hb2, hb1⟩
  unfold famOmega
  have : famP (t ^ 2) * (1 - t) + t ^ 4 / 10 = famOmegaDen t := rfl
  rw [this]
  have : 0 < t ^ 2 := by positivity
  have : 0 < 1 - t := by linarith
  positivity

theorem famLaw_sum_eventually : ∀ᶠ t in 𝓝 (0 : ℝ), ∑ j : Count, famLaw t j = 1 := by
  filter_upwards [eventually_famNear] with t h
  by_cases ht : t = 0
  · subst ht; rw [famLaw_zero]; exact reference_mass
  · obtain ⟨hω, ha0, ha1⟩ := h ht
    unfold famLaw
    simp_rw [famNu_eq_nuForm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, nuForm_sum hω ha0 ha1,
      indicator_twelve_sum]
    ring

theorem famLaw_mean_eventually :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∑ j : Count, meanCoordinate j * famLaw t j = t := by
  filter_upwards [eventually_famNear] with t h
  by_cases ht : t = 0
  · subst ht; rw [famLaw_zero]; exact reference_mean
  · obtain ⟨hω, ha0, ha1⟩ := h ht
    have hx12 : ∀ j : Count, j.val = 12 → meanCoordinate j = 1 := by
      intro j hj; rw [meanCoordinate_eq_real, hj]; norm_num
    have e : ∀ j : Count, meanCoordinate j * famLaw t j =
        (1 - famLam t) * (meanCoordinate j * nuForm (famBias t) (famOmega t) j) +
          famLam t * (if j.val = 12 then (1 : ℝ) else 0) := by
      intro j
      unfold famLaw
      rw [famNu_eq_nuForm]
      by_cases hj : j.val = 12
      · simp [hj, hx12 j hj]
      · simp [hj]
        ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, nuForm_mean hω ha0 ha1,
      indicator_twelve_sum]
    have := famLam_bias_all t
    linarith

theorem famLaw_pos_eventually : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j : Count, 0 < famLaw t j := by
  have : ∀ j : Count, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < famLaw t j / reference j := by
    intro j
    have h := (famLaw_ratio_jet j).tendsto
    exact h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rw [Filter.eventually_all]
  intro j
  filter_upwards [this j] with t ht
  exact (div_pos_iff_of_pos_right (reference_pos j)).mp ht

end BecknerOnofri.V2.FiniteState

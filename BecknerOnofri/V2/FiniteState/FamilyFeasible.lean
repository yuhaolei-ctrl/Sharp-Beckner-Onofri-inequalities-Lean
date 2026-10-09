module

public import BecknerOnofri.V2.FiniteState.FamilyIdentities

@[expose] public section

/-!
# Explicit family: mass one, mean `t`, positivity, state-zero cap (Lemma 5.19)

CROSS-CHECK ROUTE.  The manuscript proves `∑ ν_j = 1` and `∑ x_j ν_j = a` through Euler's beta
integral and conditional binomial moments; that written route is in `FamilyBeta` (theorems with
suffix `_beta`), and the downstream development (`FamilyLocal`, `FamilyComparison`, origin jets)
uses it.  Here, as an independent cross-check, they are obtained from the finite
Chu--Vandermonde-type identities for rising products
`∑_j C(12,j) (α)_j (β)_{12-j} = (α+β)_12`, `∑_j j C(12,j) (α)_j (β)_{12-j} = 12 α (α+β+1)_11`,
verified as polynomial identities of degree 12 by `ring`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Rising product `(a)_n = a (a+1) ⋯ (a+n-1)`. -/
def risingProd (a : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (a + k)

theorem risingProd_succ_left (a : ℝ) (n : ℕ) :
    risingProd a (n + 1) = a * risingProd (a + 1) n := by
  unfold risingProd
  rw [Finset.prod_range_succ']
  rw [mul_comm]
  simp only [Nat.cast_add, Nat.cast_one, add_zero, Nat.cast_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  ring

theorem risingProd_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < risingProd a n :=
  Finset.prod_pos (fun k _ => by positivity)

theorem risingProd_twelve (x : ℝ) :
    risingProd x 12 = x * risingProd (x + 1) 11 := risingProd_succ_left x 11

theorem risingProd_twelve' (x : ℝ) :
    risingProd x 12 = x * ((x + 1) * risingProd (x + 2) 10) := by
  rw [risingProd_twelve, show (11 : ℕ) = 10 + 1 from rfl, risingProd_succ_left]
  ring_nf

/-- Finite Vandermonde identity (order twelve): total mass. -/
theorem vandermonde_mass (α β : ℝ) :
    ∑ j ∈ Finset.range 13, ((12).choose j : ℝ) * risingProd α j * risingProd β (12 - j) =
      risingProd (α + β) 12 := by
  simp only [risingProd, Finset.sum_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.choose]
  ring

/-- Finite Vandermonde identity (order twelve): first moment. -/
theorem vandermonde_first (α β : ℝ) :
    ∑ j ∈ Finset.range 13,
      (j : ℝ) * (((12).choose j : ℝ) * risingProd α j * risingProd β (12 - j)) =
      12 * α * risingProd (α + β + 1) 11 := by
  simp only [risingProd, Finset.sum_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.choose]
  ring

/-- Finite Vandermonde identity (order twelve): second factorial moment. -/
theorem vandermonde_second (α β : ℝ) :
    ∑ j ∈ Finset.range 13,
      (j : ℝ) * (j - 1) * (((12).choose j : ℝ) * risingProd α j * risingProd β (12 - j)) =
      132 * α * (α + 1) * risingProd (α + β + 2) 10 := by
  simp only [risingProd, Finset.sum_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.choose]
  ring

/-- Beta-binomial probabilities with explicit parameters `α, β`. -/
def betaBinom (α β : ℝ) (j : ℕ) : ℝ :=
  ((12).choose j : ℝ) * risingProd α j * risingProd β (12 - j) / risingProd (α + β) 12

theorem betaBinom_sum {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, betaBinom α β j = 1 := by
  have hpos : 0 < risingProd (α + β) 12 := risingProd_pos (by positivity) 12
  unfold betaBinom
  rw [← Finset.sum_div, vandermonde_mass]
  exact div_self hpos.ne'

/-- `E[j] = 12 α/(α+β)`. -/
theorem betaBinom_first {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, (j : ℝ) * betaBinom α β j = 12 * α / (α + β) := by
  have hpos : 0 < risingProd (α + β + 1) 11 := risingProd_pos (by positivity) 11
  have hab : 0 < α + β := by positivity
  unfold betaBinom
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div, vandermonde_first, risingProd_twelve (α + β)]
  field_simp

/-- `E[j(j-1)] = 132 α (α+1)/((α+β)(α+β+1))`. -/
theorem betaBinom_second {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, (j : ℝ) * (j - 1) * betaBinom α β j =
      132 * α * (α + 1) / ((α + β) * (α + β + 1)) := by
  have hpos : 0 < risingProd (α + β + 2) 10 := risingProd_pos (by positivity) 10
  have hab : 0 < α + β := by positivity
  unfold betaBinom
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div, vandermonde_second, risingProd_twelve' (α + β)]
  field_simp

theorem meanCoordinate_eq_real (j : Count) : meanCoordinate j = (2 * (j.val : ℝ) - 12) / 12 := by
  unfold meanCoordinate meanCoordinateQ
  push_cast
  ring

/-- The two beta parameters `α = χ(1+a)/2`, `β = χ(1-a)/2`. -/
def famAlpha (t : ℝ) : ℝ := famChi t * (1 + famBias t) / 2
def famBeta (t : ℝ) : ℝ := famChi t * (1 - famBias t) / 2

theorem famBias_lt_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : famBias t < 1 :=
  lt_of_le_of_lt (famBias_bounds ht0.le ht1.le).2 ht1

theorem famBias_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famBias t :=
  lt_of_lt_of_le (by linarith) (famBias_bounds ht0.le ht1.le).1

theorem famAlpha_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famAlpha t := by
  have := famChi_pos ht0 ht1
  have := famBias_pos ht0 ht1
  unfold famAlpha; positivity

theorem famBeta_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famBeta t := by
  have := famChi_pos ht0 ht1
  have := famBias_lt_one ht0 ht1
  unfold famBeta
  have : 0 < 1 - famBias t := by linarith
  positivity

theorem famAlpha_add_famBeta (t : ℝ) : famAlpha t + famBeta t = famChi t := by
  unfold famAlpha famBeta; ring

theorem famNuRising_eq_betaBinom {t : ℝ} (j : Count) :
    famNuRising t j = betaBinom (famAlpha t) (famBeta t) j.val := by
  unfold famNuRising betaBinom risingProd
  rw [famAlpha_add_famBeta]
  rfl

theorem famNu_eq_betaBinom {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    famNu t j = betaBinom (famAlpha t) (famBeta t) j.val := by
  rw [famNu_eq_rising ht0 ht1, famNuRising_eq_betaBinom]

theorem famNu_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) : 0 < famNu t j := by
  rw [famNu_eq_betaBinom ht0 ht1]
  have hα := famAlpha_pos ht0 ht1
  have hβ := famBeta_pos ht0 ht1
  unfold betaBinom
  have := risingProd_pos hα j.val
  have := risingProd_pos hβ (12 - j.val)
  have := risingProd_pos (add_pos hα hβ) 12
  have hc : (0 : ℝ) < ((12).choose j.val : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.lt_succ_iff.mp j.isLt))
  positivity

/-- Normalisation of the beta-binomial component `ν`. -/
theorem famNu_sum {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∑ j : Count, famNu t j = 1 := by
  simp_rw [famNu_eq_betaBinom ht0 ht1]
  rw [Fin.sum_univ_eq_sum_range (fun j => betaBinom (famAlpha t) (famBeta t) j) 13]
  exact betaBinom_sum (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1)

/-- Mean of the component: `∑ x_j ν_j = a` (`2α/(α+β) - 1 = a`). -/
theorem famNu_mean {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ j : Count, meanCoordinate j * famNu t j = famBias t := by
  have hα := famAlpha_pos ht0 ht1
  have hβ := famBeta_pos ht0 ht1
  have hχ := famChi_pos ht0 ht1
  have h1 := betaBinom_first hα hβ
  have h0 := betaBinom_sum hα hβ
  have e : ∀ j : Count, meanCoordinate j * famNu t j =
      (1 / 6) * ((j.val : ℝ) * betaBinom (famAlpha t) (famBeta t) j.val) -
        betaBinom (famAlpha t) (famBeta t) j.val := by
    intro j
    rw [famNu_eq_betaBinom ht0 ht1, meanCoordinate_eq_real]
    ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) * betaBinom (famAlpha t) (famBeta t) j) 13,
    Fin.sum_univ_eq_sum_range (fun j => betaBinom (famAlpha t) (famBeta t) j) 13, h1, h0,
    famAlpha_add_famBeta]
  unfold famAlpha
  field_simp
  ring

theorem famL_pos {t : ℝ} (_ht0 : 0 < t) : 0 < famL t := by unfold famL; positivity

theorem famLam_nonneg {t : ℝ} (_ht0 : 0 ≤ t) : 0 ≤ famLam t := by
  unfold famLam famL; positivity

theorem famLam_lt_one {t : ℝ} (_ht0 : 0 ≤ t) : famLam t < 1 := by
  have : 0 ≤ famL t := by unfold famL; positivity
  unfold famLam
  rw [div_lt_one (by linarith)]
  linarith

/-- `(1-λ) a + λ = t`. -/
theorem famLam_bias {t : ℝ} (_ht0 : 0 ≤ t) :
    (1 - famLam t) * famBias t + famLam t = t := by
  have : 0 ≤ famL t := by unfold famL; positivity
  unfold famLam famBias
  field_simp
  ring

theorem indicator_twelve_sum :
    ∑ j : Count, (if j.val = 12 then (1 : ℝ) else 0) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j = 12 then (1 : ℝ) else 0) 13]
  simp

theorem famLaw_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) : 0 < famLaw t j := by
  have h1 := famLam_lt_one ht0.le
  have h2 := famLam_nonneg ht0.le
  have h3 := famNu_pos ht0 ht1 j
  unfold famLaw
  have : 0 ≤ famLam t * (if j.val = 12 then (1 : ℝ) else 0) := by
    split_ifs <;> simp [h2]
  nlinarith [mul_pos (sub_pos.mpr h1) h3]

theorem famLaw_sum_of_nu {t : ℝ} (hnu : ∑ j : Count, famNu t j = 1) :
    ∑ j : Count, famLaw t j = 1 := by
  unfold famLaw
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnu, indicator_twelve_sum]
  ring

theorem famLaw_sum {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∑ j : Count, famLaw t j = 1 :=
  famLaw_sum_of_nu (famNu_sum ht0 ht1)

/-- `mean (p(t)) = t`, given the component mean `∑ x_j ν_j = a`. -/
theorem famLaw_mean_of_nu {t : ℝ} (ht0 : 0 < t)
    (hnu : ∑ j : Count, meanCoordinate j * famNu t j = famBias t) : mean (famLaw t) = t := by
  have hx12 : ∀ j : Count, j.val = 12 → meanCoordinate j = 1 := by
    intro j hj; rw [meanCoordinate_eq_real, hj]; norm_num
  have e : ∀ j : Count, meanCoordinate j * famLaw t j =
      (1 - famLam t) * (meanCoordinate j * famNu t j) +
        famLam t * (if j.val = 12 then (1 : ℝ) else 0) := by
    intro j
    unfold famLaw
    by_cases hj : j.val = 12
    · simp [hj, hx12 j hj]
    · simp [hj]; ring
  unfold mean
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnu, indicator_twelve_sum]
  have := famLam_bias ht0.le
  linarith

/-- `mean (p(t)) = t`. -/
theorem famLaw_mean {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : mean (famLaw t) = t :=
  famLaw_mean_of_nu ht0 (famNu_mean ht0 ht1)

/-- Route-independent bridge: the cap `ν_0 < b_0` follows from the product ratio `ν_0/b_0 < 1`
(`ν_0/b_0 = ∏_{k<12} (χ(1-a)+2k)/(χ+k)`). -/
theorem famNu_zero_state_lt_of_ratio {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hr : ∏ k ∈ Finset.range 12, (famChi t * (1 - famBias t) + 2 * (k : ℝ)) / (famChi t + k) < 1) :
    famNu t 0 < reference 0 := by
  have hχ := famChi_pos ht0 ht1
  have e : famNu t 0 = (1 / 2) ^ 12 *
      ∏ k ∈ Finset.range 12, (famChi t * (1 - famBias t) + 2 * (k : ℝ)) / (famChi t + k) := by
    rw [famNu_eq_betaBinom ht0 ht1]
    unfold betaBinom risingProd
    rw [famAlpha_add_famBeta]
    simp only [Fin.val_zero, Finset.range_zero, Finset.prod_empty, Nat.choose_zero_right,
      Nat.cast_one, one_mul, Nat.sub_zero]
    rw [← Finset.prod_div_distrib, show ((1 : ℝ) / 2) ^ 12 = ∏ k ∈ Finset.range 12, (1 / 2 : ℝ) by simp,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    unfold famBeta
    have : 0 < famChi t + k := by positivity
    field_simp
  have hb : reference 0 = (1 / 2) ^ 12 := by
    unfold reference referenceQ
    push_cast
    norm_num
  rw [e, hb]
  have : (0 : ℝ) < (1 / 2) ^ 12 := by positivity
  nlinarith

/-- State-zero cap for the beta-binomial component: `ν_0 < b_0`. -/
theorem famNu_zero_state_lt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famNu t 0 < reference 0 := by
  have hχ := famChi_pos ht0 ht1
  have hca : 11 / 2 < famChi t * famBias t := by
    have := famChi_mul_bias_ge ht0 ht1; linarith
  exact famNu_zero_state_lt_of_ratio ht0 ht1
    (state_zero_ratio_lt_one hχ (famBias_lt_one ht0 ht1) hca)

theorem famLaw_zero_state_lt_of_nu {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h4 : famNu t 0 < reference 0) : famLaw t 0 < reference 0 := by
  have h1 := famLam_lt_one ht0.le
  have h2 := famLam_nonneg ht0.le
  have h3 := famNu_pos ht0 ht1 0
  unfold famLaw
  have h12 : ¬ ((0 : Count).val = 12) := by decide
  simp only [h12, ↓reduceIte, mul_zero, add_zero]
  nlinarith [mul_pos (sub_pos.mpr h1) h3]

theorem famLaw_zero_state_lt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famLaw t 0 < reference 0 :=
  famLaw_zero_state_lt_of_nu ht0 ht1 (famNu_zero_state_lt ht0 ht1)

/-- Route-independent assembly of feasibility from mass, mean and the state-zero cap. -/
theorem famLaw_feasibleAt_of_parts {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hsum : ∑ j : Count, famLaw t j = 1) (hmean : mean (famLaw t) = t)
    (hcap : famLaw t 0 < reference 0) : FeasibleAt t (famLaw t) := by
  refine ⟨⟨fun j => (famLaw_pos ht0 ht1 j).le, hsum, ?_⟩, hmean⟩
  have hb : reference 0 = 1 / 4096 := by
    unfold reference referenceQ; push_cast; norm_num
  linarith

/-- **Lemma 5.19 (feasibility part)**: for `0 < t < 1`, `p(t)` is positive, lies in `𝒫_t`,
and `p_0(t) < 2^{-12}`. -/
theorem famLaw_feasibleAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : FeasibleAt t (famLaw t) :=
  famLaw_feasibleAt_of_parts ht0 ht1 (famLaw_sum ht0 ht1) (famLaw_mean ht0 ht1)
    (famLaw_zero_state_lt ht0 ht1)

theorem famLaw_zero_state_lt_one_div {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famLaw t 0 < 1 / 4096 := by
  have := famLaw_zero_state_lt ht0 ht1
  have hb : reference 0 = 1 / 4096 := by
    unfold reference referenceQ; push_cast; norm_num
  linarith

end BecknerOnofri.V2.FiniteState

module

public import BecknerOnofri.V2.FiniteState.AffineCertificate
public import BecknerOnofri.SpinAlgebra
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# Lemma 5.17 (fixed-mean curvature), affine-residual route

Compiled (sorry-free).  Source proof: subtract `α_s + β_s x_j` inside each feature sum
(the two constraints `∑ v = 0`, `∑ x_j v_j = 0` remove it), weighted Cauchy--Schwarz for each `s`,
sum over `s`, then use the thirteen rational bounds of Appendix B.3 together with
`p_0 ≤ 1/4096` and `∑ p = 1`.  It does NOT use `Spin.fixed_mean_curvature`,
`Spin.corrected_seminorm_bound`, the vertex energies or the correcting vectors.
Reused generic items: `Spin.quadratic_eq_sum`, `Spin.weight_nonneg`, `Spin.Feasible`, `Spin.mean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Real residual `∑_s w_s (A_{s,j} - α_s - β_s x_j)^2`. -/
def residual (j : Count) : ℝ :=
  ∑ s : Order, weight s * (moment s j - (alphaQ s : ℝ) - (betaQ s : ℝ) * meanCoordinate j) ^ 2

theorem residual_eq_cast (j : Count) : residual j = (residualQ j : ℝ) := by
  simp only [residual, residualQ, weight, moment, meanCoordinate]
  push_cast
  rfl

theorem residual_lt_cap (j : Count) :
    residual j < (if j = 0 then (6 : ℝ) else 179 / 200) := by
  rw [residual_eq_cast]
  have h := residualQ_lt_cap j
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte] at h ⊢
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    norm_num at h'
    exact h'
  · simp only [hj, ↓reduceIte] at h ⊢
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    norm_num at h'
    exact h'

theorem residual_le_cap (j : Count) : residual j ≤ 179 / 200 + (if j = 0 then (6 : ℝ) else 0) := by
  have h := residual_lt_cap j
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte] at h ⊢; linarith
  · simp only [hj, ↓reduceIte] at h ⊢; linarith

/-- Affine removal: for a vector with zero mass and zero mean, the feature sum is unchanged
when `α + β x_j` is subtracted from the feature. -/
theorem feature_sum_affine {v : Count → ℝ} (hmass : (∑ j : Count, v j) = 0) (hmean : mean v = 0)
    (s : Order) (α β : ℝ) :
    (∑ j : Count, moment s j * v j) =
      ∑ j : Count, (moment s j - α - β * meanCoordinate j) * v j := by
  have h1 : (∑ j : Count, (moment s j - α - β * meanCoordinate j) * v j) =
      (∑ j : Count, moment s j * v j) - α * (∑ j : Count, v j) -
        β * (∑ j : Count, meanCoordinate j * v j) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, hmass]
  have : (∑ j : Count, meanCoordinate j * v j) = 0 := hmean
  rw [this]
  ring

/-- Weighted Cauchy--Schwarz, one feature:
`(∑ r_j v_j)^2 ≤ (∑ p_j r_j^2) (∑ v_j^2 / p_j)`. -/
theorem weighted_cauchy_schwarz (p r v : Count → ℝ) (hp : ∀ j, 0 < p j) :
    (∑ j : Count, r j * v j) ^ 2 ≤
      (∑ j : Count, p j * r j ^ 2) * (∑ j : Count, v j ^ 2 / p j) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset Count)
    (r := fun j => r j * v j) (f := fun j => p j * r j ^ 2) (g := fun j => v j ^ 2 / p j)
    (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
    (fun j _ => div_nonneg (sq_nonneg _) (hp j).le)
  intro j _
  have hpj := (hp j).ne'
  show (r j * v j) ^ 2 ≤ p j * r j ^ 2 * (v j ^ 2 / p j)
  have e : p j * r j ^ 2 * (v j ^ 2 / p j) = (r j * v j) ^ 2 := by
    field_simp
  rw [e]

/-- **Lemma 5.17.** `p ∈ 𝒫` with positive entries, `∑ v = 0`, `∑ x_j v_j = 0`:
`v^T W v ≤ (9/10) ∑ v_j^2 / p_j`. -/
theorem fixed_mean_curvature_affine {p v : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j, 0 < p j)
    (hmass : (∑ j : Count, v j) = 0) (hmean : mean v = 0) :
    quadratic v ≤ (9 / 10) * (∑ j : Count, v j ^ 2 / p j) := by
  set S : ℝ := ∑ j : Count, v j ^ 2 / p j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le)
  -- per-feature Cauchy--Schwarz after affine subtraction
  have hfeat (s : Order) :
      (∑ j : Count, moment s j * v j) ^ 2 ≤
        (∑ j : Count, p j * (moment s j - (alphaQ s : ℝ) - (betaQ s : ℝ) * meanCoordinate j) ^ 2) * S := by
    rw [feature_sum_affine hmass hmean s (alphaQ s) (betaQ s)]
    exact weighted_cauchy_schwarz p _ v hpos
  -- sum over s with weights
  have hq : quadratic v ≤
      ∑ s : Order, weight s *
        ((∑ j : Count, p j * (moment s j - (alphaQ s : ℝ) - (betaQ s : ℝ) * meanCoordinate j) ^ 2) * S) := by
    rw [quadratic_eq_sum]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hfeat s) (weight_nonneg s))
  -- exchange the order of summation: ∑_s w_s ∑_j p_j R_{sj}^2 = ∑_j p_j residual j
  have hswap : (∑ s : Order, weight s *
        ((∑ j : Count, p j * (moment s j - (alphaQ s : ℝ) - (betaQ s : ℝ) * meanCoordinate j) ^ 2) * S)) =
      (∑ j : Count, p j * residual j) * S := by
    simp only [residual, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro s _
    ring
  -- thirteen rational bounds, mass one, cap on state 0
  have hcoef : (∑ j : Count, p j * residual j) ≤ 45899 / 51200 := by
    have h1 : (∑ j : Count, p j * residual j) ≤
        ∑ j : Count, p j * (179 / 200 + (if j = 0 then (6 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (residual_le_cap j) (hpos j).le)
    have h2 : (∑ j : Count, p j * (179 / 200 + (if j = 0 then (6 : ℝ) else 0))) =
        179 / 200 * (∑ j : Count, p j) + (∑ j : Count, p j * (if j = 0 then (6 : ℝ) else 0)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h4 : (∑ j : Count, p j * (if j = 0 then (6 : ℝ) else 0)) = 6 * p 0 := by
      simp [mul_comm]
    have h3 := hp.2.2
    rw [hp.2.1] at h2
    linarith
  calc quadratic v ≤ (∑ j : Count, p j * residual j) * S := hq.trans hswap.le
    _ ≤ (45899 / 51200) * S := mul_le_mul_of_nonneg_right hcoef hS0
    _ ≤ (9 / 10) * S := mul_le_mul_of_nonneg_right (by norm_num) hS0

end BecknerOnofri.V2.FiniteState

module

public import BecknerOnofri.V2.FiniteState.FamilyDefs

@[expose] public section

/-!
# Explicit family: value at zero and rising-factorial / rational-product equality

Source: Lemma 5.19 and Appendix A.3 (`d12-spin-eq:beta`, `d12-spin-eq:h`,
`d12-spin-eq:rationalfamily`).  Nothing here divides by `t` at `t = 0`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

@[simp] theorem famL_zero : famL 0 = 0 := by simp [famL]
@[simp] theorem famLam_zero : famLam 0 = 0 := by simp [famLam]
@[simp] theorem famBias_zero : famBias 0 = 0 := by simp [famBias]
@[simp] theorem famOmega_zero : famOmega 0 = 0 := by simp [famOmega]

theorem reference_eq (j : Count) : reference j = ((12).choose j.val : ℝ) / 4096 := by
  unfold reference referenceQ
  push_cast
  rfl

/-- At `t = 0` the rational beta-binomial vector is the fair binomial vector. -/
theorem famNu_zero (j : Count) : famNu 0 j = reference j := by
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  simp only [famNu, famBias_zero, famOmega_zero, reference, referenceQ]
  simp only [add_zero, mul_zero, Finset.prod_const, Finset.card_range, div_one, sub_zero, one_pow]
  rw [mul_assoc, ← pow_add, show j.val + (12 - j.val) = 12 by omega]
  push_cast
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  norm_num
  ring

theorem famLaw_zero : famLaw 0 = reference := by
  funext j
  simp [famLaw, famNu_zero]

theorem prod_range_const_mul (c : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    ∏ k ∈ Finset.range n, (c * g k) = c ^ n * ∏ k ∈ Finset.range n, g k := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- The rational product form equals the rising-factorial form on `(0,1)`:
`d12-spin-eq:beta` ⇔ `d12-spin-eq:rationalfamily`. -/
theorem famNu_eq_rising {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    famNu t j = famNuRising t j := by
  have hχ : 0 < famChi t := famChi_pos ht0 ht1
  have hω : famOmega t = (famChi t)⁻¹ := by
    have := famOmega_mul_famChi ht0 ht1
    field_simp
    linarith
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  set χ := famChi t with hχdef
  have e1 : ∏ k ∈ Finset.range j.val, (χ * (1 + famBias t) / 2 + (k : ℝ)) =
      χ ^ j.val * ∏ k ∈ Finset.range j.val, ((1 + famBias t) / 2 + (k : ℝ) * famOmega t) := by
    rw [← prod_range_const_mul]
    apply Finset.prod_congr rfl
    intro k _
    rw [hω]; field_simp
  have e2 : ∏ k ∈ Finset.range (12 - j.val), (χ * (1 - famBias t) / 2 + (k : ℝ)) =
      χ ^ (12 - j.val) * ∏ k ∈ Finset.range (12 - j.val), ((1 - famBias t) / 2 + (k : ℝ) * famOmega t) := by
    rw [← prod_range_const_mul]
    apply Finset.prod_congr rfl
    intro k _
    rw [hω]; field_simp
  have e3 : ∏ k ∈ Finset.range 12, (χ + (k : ℝ)) =
      χ ^ 12 * ∏ k ∈ Finset.range 12, (1 + (k : ℝ) * famOmega t) := by
    rw [← prod_range_const_mul]
    apply Finset.prod_congr rfl
    intro k _
    rw [hω]; field_simp
  have hpow : χ ^ 12 = χ ^ j.val * χ ^ (12 - j.val) := by
    rw [← pow_add]; congr 1; omega
  unfold famNu famNuRising
  rw [e1, e2, e3, hpow]
  have h1 : (0 : ℝ) < χ ^ j.val := pow_pos hχ _
  have h2 : (0 : ℝ) < χ ^ (12 - j.val) := pow_pos hχ _
  have h3 : ∏ k ∈ Finset.range 12, (1 + (k : ℝ) * famOmega t) ≠ 0 := by
    have hω0 : 0 ≤ famOmega t := by rw [hω]; positivity
    exact (Finset.prod_pos (fun k _ => by positivity)).ne'

  rw [div_eq_div_iff h3 (by positivity)]
  ring

end BecknerOnofri.V2.FiniteState

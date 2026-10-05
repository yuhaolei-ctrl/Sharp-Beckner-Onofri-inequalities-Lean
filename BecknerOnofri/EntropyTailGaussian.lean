module

public import BecknerOnofri.EntropyTailScalarBasic
public import BecknerOnofri.ComplementGap
public import Legacy.BecknerOnofri.GaussianTheta

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

/-- The half-integer Gaussian scale from the manuscript. -/
theorem half_parameter_le_log {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1/2) ≤ Real.log (1 + 1/(n : ℝ)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1/(n : ℝ) by positivity)
  have he : 2*(1/(n : ℝ))/(1/(n : ℝ)+2) = 1/((n : ℝ)+1/2) := by
    field_simp
    <;> ring
  rwa [he] at h

theorem scalarCoefficient_gaussian {n : ℕ} (hn : 0 < n) (j : ℕ) :
    scalarCoefficient n j ≤ Real.exp (-(j : ℝ)^2/((n : ℝ)+1/2)) := by
  rw [scalarCoefficient_eq]
  apply (Legacy.D10.binomialCoeffReal_gaussian n j hn).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (half_parameter_le_log hn) (sq_nonneg (j : ℝ))
  convert! neg_le_neg h using 1 <;> ring

theorem scalarProduct_gaussian {n : ℕ} (hn : 0 < n) (k : Frequency 12) :
    (∏ i : Fin 12, scalarCoefficient n (k i).natAbs) ≤
      Legacy.BecknerOnofri.GaussianLattice.gaussian (1/((n : ℝ)+1/2)) k := by
  rw [Legacy.BecknerOnofri.GaussianLattice.gaussian_eq_product]
  apply Finset.prod_le_prod₀
  · intro i _
    unfold scalarCoefficient
    positivity
  · intro i _
    have h := scalarCoefficient_gaussian hn (k i).natAbs
    simp only [Nat.cast_natAbs, Int.cast_abs, sq_abs] at h
    convert! h using 1 <;> congr 1 <;> ring

theorem scalarTailWeight_nonneg (k : Frequency 12) : 0 ≤ scalarTailWeight k := by
  unfold scalarTailWeight
  split_ifs <;> positivity

theorem scalarTailWeight_le_one (k : Frequency 12) : scalarTailWeight k ≤ 1 := by
  unfold scalarTailWeight
  split_ifs with hk
  · have hn : k ≠ 0 := by
      intro hz
      subst k
      obtain ⟨i,hi⟩ := hk
      simp at hi
    have hl : 1 ≤ latticeSquare k := by
      have := (latticeSquare_eq_zero_iff k).not.mpr hn
      omega
    have hp : frequencyLength k^12 = (latticeSquare k : ℝ)^6 := by
      have h := frequencyLength_pow_eq k
      norm_num only [Nat.cast_ofNat, show (12 : ℝ)/2 = 6 by norm_num, Real.rpow_ofNat] at h
      exact h
    rw [hp]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hl))
  · norm_num

open Legacy.BecknerOnofri.GaussianLattice in
theorem gaussianTail_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun k : Frequency 12 => scalarTailWeight k *
      Real.exp (-η * ∑ i : Fin 12, (k i : ℝ)^2)) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (scalarTailWeight_nonneg k) (Real.exp_pos _).le) ?_
    (summable_gaussian hη)
  intro k
  exact mul_le_of_le_one_left (Real.exp_pos _).le (scalarTailWeight_le_one k)

theorem scalarTail_le_gaussianTail {n : ℕ} (hn : 0 < n) :
    scalarTail n ≤ gaussianTail (1/((n : ℝ)+1/2)) := by
  apply (scalarTail_summable n).tsum_le_tsum _ (gaussianTail_summable (by positivity))
  intro k
  exact mul_le_mul_of_nonneg_left (scalarProduct_gaussian hn k) (scalarTailWeight_nonneg k)

#print axioms scalarTail_le_gaussianTail
end BecknerOnofri.HighDim.EntropyTail

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

@[expose] public section

/-! Explicit complete infinite tails for the two circle heat derivative representations. -/
noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeatDerivativeTail

def fourierTerm (t : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ)+2)^2 * Real.exp (-Real.pi*t*(((m : ℝ)+2)^2-1))
def fourierTail (t : ℝ) : ℝ := ∑' m : ℕ, fourierTerm t m

def poissonTerm (A : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ)+1)^2 * Real.exp (-A*((m : ℝ)+1)^2/2)
def poissonTail (A : ℝ) : ℝ := ∑' m : ℕ, poissonTerm A m

/-- The first shifted quadratic geometric series, proved from the actual binomial series. -/
theorem hasSum_shift_one_sq {q : ℝ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((m : ℝ)+1)^2*q^(m+1))
      (q*(2/(1-q)^3-1/(1-q)^2)) := by
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hq
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hq
  convert! ((h2.mul_left 2).sub h1).mul_left q using 1
  · ext m
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat, Nat.choose_one_right,
      Nat.cast_one, pow_succ]
    ring
  · ring

/-- The second shifted quadratic geometric series. -/
theorem hasSum_shift_two_sq {q : ℝ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((m : ℝ)+2)^2*q^(m+1))
      (q*(2/(1-q)^3+1/(1-q)^2+1/(1-q))) := by
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hq
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hq
  have h0 := hasSum_geometric_of_norm_lt_one hq
  convert! (((h2.mul_left 2).add h1).add h0).mul_left q using 1
  · ext m
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat, Nat.choose_one_right,
      Nat.cast_one, pow_succ]
    ring
  · simp only [one_div]
    ring

theorem geometric_fourier_hasSum :
    HasSum (fun m : ℕ => ((m : ℝ)+2)^2*(1/8:ℝ)^(m+1)) (233/343:ℝ) := by
  convert! hasSum_shift_two_sq (q:= (1/8:ℝ)) (by norm_num) using 1 <;> norm_num

theorem geometric_poisson_hasSum :
    HasSum (fun m : ℕ => ((m : ℝ)+1)^2*(1/100:ℝ)^(m+1)) (10100/970299:ℝ) := by
  convert! hasSum_shift_one_sq (q:= (1/100:ℝ)) (by norm_num) using 1 <;> norm_num

theorem exp_neg_nine_quarters_le : Real.exp (-(9/4:ℝ)) ≤ (1/8:ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤9/4) 6
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem exp_neg_six_le : Real.exp (-6) ≤ (1/100:ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤6) 6
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem fourierTerm_le {t : ℝ} (ht : 1/4 ≤ t) (m : ℕ) :
    fourierTerm t m ≤ ((m : ℝ)+2)^2*(1/8:ℝ)^(m+1) := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hpt : (3/4:ℝ) ≤ Real.pi*t := by
    have := mul_le_mul Real.pi_gt_three.le ht (by norm_num : (0:ℝ)≤1/4)
      Real.pi_pos.le
    nlinarith
  have hs : 3*((m:ℝ)+1) ≤ ((m:ℝ)+2)^2-1 := by nlinarith [sq_nonneg (m:ℝ)]
  have hp := mul_le_mul_of_nonneg_left hs (by linarith : 0≤Real.pi*t)
  have hp' := mul_le_mul_of_nonneg_right hpt (by positivity : 0≤3*((m:ℝ)+1))
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    Real.exp (-Real.pi*t*(((m:ℝ)+2)^2-1)) ≤
        Real.exp (-(9/4:ℝ))^(m+1) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith only [hp,hp']
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_nine_quarters_le _

theorem summable_fourierTail {t : ℝ} (ht : 1/4 ≤ t) : Summable (fourierTerm t) :=
  geometric_fourier_hasSum.summable.of_nonneg_of_le
    (fun m => by unfold fourierTerm; positivity) (fourierTerm_le ht)

theorem fourierTail_le {t : ℝ} (ht : 1/4 ≤ t) : fourierTail t ≤ (233/343:ℝ) := by
  calc
    _ ≤ ∑' m : ℕ, ((m:ℝ)+2)^2*(1/8:ℝ)^(m+1) :=
      (summable_fourierTail ht).tsum_le_tsum (fourierTerm_le ht)
        geometric_fourier_hasSum.summable
    _ = _ := geometric_fourier_hasSum.tsum_eq

/-- Monotonicity of `A exp(-A c)` on the required range, proved without any tail assumption. -/
theorem scaled_exp_le {A c : ℝ} (hA : 12 ≤ A) (hc : 1/2 ≤ c) :
    A*Real.exp (-A*c) ≤ 12*Real.exp (-12*c) := by
  have hAc : 0 ≤ (A-12)*c := mul_nonneg (by linarith) (by linarith)
  have he := Real.add_one_le_exp ((A-12)*c)
  have hprod := mul_nonneg (by linarith : 0≤A-12) (by linarith : 0≤c-1/2)
  have hbase : A ≤ 12*Real.exp ((A-12)*c) := by nlinarith
  calc
    _ ≤ 12*Real.exp ((A-12)*c)*Real.exp (-A*c) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 1 <;> ring

theorem exp_square_le_geometric (m : ℕ) :
    Real.exp (-6*((m:ℝ)+1)^2) ≤ (1/100:ℝ)^(m+1) := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  calc
    _ ≤ Real.exp (-6)^(m+1) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [sq_nonneg (m:ℝ)]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_six_le _

theorem poissonTerm_le {A : ℝ} (hA : 12 ≤ A) (m : ℕ) :
    poissonTerm A m ≤ ((m:ℝ)+1)^2*(1/100:ℝ)^(m+1) := by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply le_trans _ (exp_square_le_geometric m)
  apply Real.exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_right hA (sq_nonneg ((m:ℝ)+1))
  linarith

theorem summable_poissonTail {A : ℝ} (hA : 12 ≤ A) : Summable (poissonTerm A) :=
  geometric_poisson_hasSum.summable.of_nonneg_of_le
    (fun m => by unfold poissonTerm; positivity) (poissonTerm_le hA)

theorem poisson_scaled_term_le {A : ℝ} (hA : 12 ≤ A) (m : ℕ) :
    A*poissonTerm A m ≤ 12*(((m:ℝ)+1)^2*(1/100:ℝ)^(m+1)) := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hc : (1/2:ℝ) ≤ ((m:ℝ)+1)^2/2 := by nlinarith [sq_nonneg (m:ℝ)]
  have he := scaled_exp_le hA hc
  have hg := exp_square_le_geometric m
  have he0 : A*Real.exp (-A*((m:ℝ)+1)^2/2) ≤
      12*Real.exp (-6*((m:ℝ)+1)^2) := by
    convert! he using 1 <;> ring_nf
  have he' : A*Real.exp (-A*((m:ℝ)+1)^2/2) ≤ 12*(1/100:ℝ)^(m+1) :=
    he0.trans (mul_le_mul_of_nonneg_left hg (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left he' (sq_nonneg ((m:ℝ)+1))
  unfold poissonTerm
  nlinarith only [hmul]

theorem poissonTail_scaled_le {A : ℝ} (hA : 12 ≤ A) :
    (25/4:ℝ)*A*poissonTail A ≤ (757500/970299:ℝ) := by
  have ht : A*poissonTail A ≤ 12*(10100/970299:ℝ) := by
    calc
      _ = ∑' m : ℕ, A*poissonTerm A m := by rw [poissonTail, tsum_mul_left]
      _ ≤ ∑' m : ℕ, 12*(((m:ℝ)+1)^2*(1/100:ℝ)^(m+1)) :=
        ((summable_poissonTail hA).mul_left A).tsum_le_tsum (poisson_scaled_term_le hA)
          (geometric_poisson_hasSum.summable.mul_left 12)
      _ = _ := by rw [tsum_mul_left, geometric_poisson_hasSum.tsum_eq]
  nlinarith only [ht]

theorem poissonTail_scaled_lt_one {A : ℝ} (hA : 12 ≤ A) :
    (25/4:ℝ)*A*poissonTail A < 1 :=
  (poissonTail_scaled_le hA).trans_lt (by norm_num)

#print axioms fourierTail_le
#print axioms poissonTail_scaled_le
#print axioms poissonTail_scaled_lt_one
end Legacy.BecknerOnofri.CircleHeatDerivativeTail

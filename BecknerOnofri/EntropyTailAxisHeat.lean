import BecknerOnofri.EntropyTailAxisFactors
import BecknerOnofri.EntropyTailHeat
import BecknerOnofri.SpectralSliceBound

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.ThetaDomination

def axisTerm (s : ℝ) (n : ℕ) (j : ℤ) : ℝ :=
  scalarCoefficient n j.natAbs*Real.exp (-s*(j : ℝ)^2)

theorem axisTerm_nonneg (s : ℝ) (n : ℕ) (j : ℤ) : 0 ≤ axisTerm s n j :=
  mul_nonneg (scalarCoefficient_nonneg _ _) (Real.exp_pos _).le

theorem axisTerm_summable {s : ℝ} (hs : 0 < s) (n : ℕ) : Summable (axisTerm s n) := by
  apply Summable.of_nonneg_of_le (axisTerm_nonneg s n) _ (summable_realTheta hs)
  intro j
  have hc : scalarCoefficient n j.natAbs ≤ 1 := by
    rw [scalarCoefficient_eq]
    exact CosineMixtureTransfer.coeff_le_one _ _
  exact mul_le_of_le_one_left (Real.exp_pos _).le hc

theorem axisTerm_even (s : ℝ) (n : ℕ) : Function.Even (axisTerm s n) := by
  intro j
  simp only [axisTerm, Int.natAbs_neg, Int.cast_neg, neg_sq]

theorem axisTerm_nat (s : ℝ) (n j : ℕ) :
    axisTerm s n (j : ℤ) = scalarCoefficient n j*Real.exp (-s*(j : ℝ)^2) := by
  simp only [axisTerm, Int.natAbs_natCast, Int.cast_natCast]

theorem axisTerm_zero (s : ℝ) (n : ℕ) : axisTerm s n 0 = 1 := by
  simp [axisTerm, scalarCoefficient_eq, Legacy.D10.binomialCoeffReal]

theorem axisTerm_tsum {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∑' j : ℤ, axisTerm s n j) = axisLow s n+axisHigh s n := by
  have h := SpectralSlice.even_integer_sum (axisTerm_even s n) (axisTerm_summable hs n)
  have hsum : Summable (fun j : ℕ => axisTerm s n ((j : ℤ)+1)) :=
    (axisTerm_summable hs n).comp_injective (fun a b h => by omega)
  rw [h, axisTerm_zero, hsum.tsum_eq_zero_add]
  have he (j : ℕ) : axisTerm s n (((j+1 : ℕ) : ℤ)+1) =
      scalarCoefficient n (j+2)*Real.exp (-s*(j+2 : ℝ)^2) := by
    rw [show (((j+1 : ℕ) : ℤ)+1) = ((j+2 : ℕ) : ℤ) by omega, axisTerm_nat]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
  simp_rw [he]
  have h1 : axisTerm s n ((0 : ℕ) : ℤ)+0 = 1 := by simp [axisTerm_zero]
  have ht1 : axisTerm s n (((0 : ℕ) : ℤ)+1) = scalarCoefficient n 1*Real.exp (-s) := by
    norm_num [axisTerm]
  rw [ht1]
  unfold axisLow axisHigh
  ring

#print axioms axisTerm_tsum
end BecknerOnofri.HighDim.EntropyTail

module

public import BecknerOnofri.SpinProductGradientDefinitions
public import BecknerOnofri.SpinProductMoments
public import BecknerOnofri.SpinSparseVertices

@[expose] public section

/-! Explicit polynomial factor of the nonaffine gradient near mean zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def smallGradientFactor (t : ℝ) (j : Count) : ℝ :=
  2*∑ l : Fin 11,weight l.succ*(moment l.succ j*t^l.val+
    (l.val+1:ℝ)*t^(2*l.val+2)-(l.val+2:ℝ)*meanCoordinate j*t^(2*l.val+1))

theorem first_spin_moment (j : Count) : moment 0 j=meanCoordinate j := by
  fin_cases j <;> norm_num [moment,momentQ,meanCoordinate,meanCoordinateQ,Nat.choose,
    Finset.sum_range_succ]

theorem interaction_product (t : ℝ) (j : Count) :
    (∑ k : Count,interaction j k*productProbability t k)=
      ∑ s : Order,weight s*moment s j*t^(s.val+1) := by
  simp only [interaction_eq,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← productProbability_moment t s,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem productGradientCorrection_factor (t : ℝ) (j : Count) :
    productGradientCorrection t j=t^2*smallGradientFactor t j := by
  unfold productGradientCorrection
  rw [interaction_product,productProbability_quadratic]
  unfold productAffineCoefficient smallGradientFactor
  simp only [Finset.sum_mul,← Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,zero_add,first_spin_moment]
  have hz : weight 0*meanCoordinate j*t^(0+1)-weight 0*t^(2*(0+1))-
      weight 0*(0+1:ℝ)*t^(2*0+1)*(meanCoordinate j-t)=0 := by ring
  norm_num only [Nat.reduceAdd,Nat.reduceMul,pow_one,Nat.cast_zero,zero_add,
    Nat.cast_one,one_mul,mul_one] at hz ⊢
  rw [hz,zero_add]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one,Nat.mul_add,Nat.mul_one,pow_add,pow_succ]
  ring

#print axioms productGradientCorrection_factor
end BecknerOnofri.HighDim.Spin

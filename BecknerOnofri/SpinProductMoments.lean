module

public import BecknerOnofri.SpinProductProbability

@[expose] public section

/-! Exact Fourier-spin moments of the product comparison law, proved as
polynomial identities for every real parameter. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem productProbability_moment (t : ℝ) (s : Order) :
    (∑ j : Count,moment s j*productProbability t j)=t^(s.val+1) := by
  fin_cases s <;>
    norm_num [moment,momentQ,productProbability,reference,referenceQ,
      Fin.sum_univ_succ,Finset.sum_range_succ,Nat.choose] <;> ring

theorem productProbability_quadratic (t : ℝ) :
    quadratic (productProbability t)=∑ s : Order,weight s*t^(2*(s.val+1)) := by
  rw [quadratic_eq_sum]
  simp_rw [productProbability_moment,← pow_mul]
  congr 1
  ext s
  rw [Nat.mul_comm (s.val+1) 2]

#print axioms productProbability_quadratic
end BecknerOnofri.HighDim.Spin

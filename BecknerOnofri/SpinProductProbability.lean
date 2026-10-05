import BecknerOnofri.SpinProductDefinitions
import BecknerOnofri.SpinAlgebra

/-! Actual normalization, mean and feasibility of the product comparison law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem productProbability_formula (t : ℝ) (j : Count) :
    productProbability t j=((12:ℕ).choose j.val:ℝ)*((1+t)/2)^j.val*((1-t)/2)^(12-j.val) := by
  unfold productProbability reference referenceQ
  push_cast
  rw [div_pow,div_pow]
  have hj : j.val+(12-j.val)=12 := by omega
  have hpow : (2:ℝ)^j.val*2^(12-j.val)=4096 := by rw [← pow_add,hj]; norm_num
  calc
    _ = ((12:ℕ).choose j.val:ℝ)*((1+t)^j.val*(1-t)^(12-j.val))/4096 := by ring
    _ = ((12:ℕ).choose j.val:ℝ)*((1+t)^j.val*(1-t)^(12-j.val))/
        ((2:ℝ)^j.val*2^(12-j.val)) := by rw [hpow]
    _ = _ := by ring

theorem productProbability_mass (t : ℝ) : (∑ j : Count,productProbability t j)=1 := by
  norm_num [productProbability,reference,referenceQ,Nat.choose,Fin.sum_univ_succ]
  ring

theorem productProbability_mean (t : ℝ) : mean (productProbability t)=t := by
  norm_num [mean,productProbability,reference,referenceQ,meanCoordinate,meanCoordinateQ,
    Nat.choose,Fin.sum_univ_succ]
  ring

theorem productProbability_nonneg {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    ∀ j,0≤productProbability t j := by
  intro j
  unfold productProbability
  exact mul_nonneg (mul_nonneg (reference_pos j).le (pow_nonneg (by linarith) _))
    (pow_nonneg (by linarith) _)

theorem productProbability_pos {t : ℝ} (ht : -1<t) (ht1 : t<1) :
    ∀ j,0<productProbability t j := by
  intro j
  unfold productProbability
  exact mul_pos (mul_pos (reference_pos j) (pow_pos (by linarith) _))
    (pow_pos (by linarith) _)

theorem productProbability_feasible {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    FeasibleAt t (productProbability t) := by
  refine ⟨⟨productProbability_nonneg ht ht1,productProbability_mass t,?_⟩,productProbability_mean t⟩
  have hpow : (1-t)^12≤(1:ℝ)^12 := pow_le_pow_left₀ (by linarith) (by linarith) 12
  norm_num [productProbability,reference,referenceQ] at *
  linarith

#print axioms productProbability_feasible
end BecknerOnofri.HighDim.Spin

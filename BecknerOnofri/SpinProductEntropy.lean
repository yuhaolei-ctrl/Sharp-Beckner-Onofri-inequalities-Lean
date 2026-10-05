import BecknerOnofri.SpinProductProbability
import BecknerOnofri.SpinBinaryCost
import BecknerOnofri.SpinSparseVertices

/-! Exact entropy of the source's product-spin comparison law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem productProbability_log_ratio {t : ℝ} (ht : -1<t) (ht1 : t<1) (j : Count) :
    Real.log (productProbability t j/reference j)=
      6*(Real.log (1+t)+Real.log (1-t))+
        6*(Real.log (1+t)-Real.log (1-t))*meanCoordinate j := by
  have hratio : productProbability t j/reference j=(1+t)^j.val*(1-t)^(12-j.val) := by
    unfold productProbability
    field_simp [(reference_pos j).ne']
  rw [hratio,Real.log_mul (pow_ne_zero _ (by linarith : 1+t≠0))
    (pow_ne_zero _ (by linarith : 1-t≠0)),Real.log_pow,Real.log_pow,meanCoordinate_eq]
  rw [Nat.cast_sub (show j.val≤12 by omega)]
  push_cast
  ring

theorem productProbability_entropy {t : ℝ} (ht : -1<t) (ht1 : t<1) :
    relativeEntropy (productProbability t) reference=12*binaryCost t := by
  unfold relativeEntropy
  simp_rw [productProbability_log_ratio ht ht1]
  have he : (∑ j : Count,productProbability t j*
      (6*(Real.log (1+t)+Real.log (1-t))+
        6*(Real.log (1+t)-Real.log (1-t))*meanCoordinate j))=
      6*(Real.log (1+t)+Real.log (1-t))*(∑ j : Count,productProbability t j)+
        6*(Real.log (1+t)-Real.log (1-t))*mean (productProbability t) := by
    simp only [mean,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,productProbability_mass,productProbability_mean]
  unfold binaryCost
  ring

#print axioms productProbability_entropy
end BecknerOnofri.HighDim.Spin

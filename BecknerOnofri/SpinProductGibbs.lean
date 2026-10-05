import BecknerOnofri.SpinProductGradientDefinitions
import BecknerOnofri.SpinProductEntropy
import BecknerOnofri.SpinFiniteGibbs

/-! The source's exponential-moment reduction with the actual product law
and its actual nonaffine energy gradient, without a gradient hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem productGradientCorrection_centered (t : ℝ) :
    (∑ j : Count,productProbability t j*productGradientCorrection t j)=0 := by
  have hmat : (∑ j : Count,productProbability t j*
      (∑ k : Count,interaction j k*productProbability t k))=quadratic (productProbability t) := by
    simp only [quadratic,Finset.mul_sum,mul_assoc]
  have hmean : (∑ j : Count,productProbability t j*(meanCoordinate j-t))=
      mean (productProbability t)-t*(∑ j : Count,productProbability t j) := by
    simp only [mean,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  let M : Count → ℝ := fun j => ∑ k : Count,interaction j k*productProbability t k
  have he : (∑ j : Count,productProbability t j*productGradientCorrection t j)=
      2*(∑ j : Count,productProbability t j*M j)-
      2*quadratic (productProbability t)*(∑ j : Count,productProbability t j)-
      2*productAffineCoefficient t*(∑ j : Count,productProbability t j*(meanCoordinate j-t)) := by
    change (∑ j : Count,productProbability t j*(2*(M j-quadratic (productProbability t)-
      productAffineCoefficient t*(meanCoordinate j-t))))=_
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,show (∑ j : Count,productProbability t j*M j)=quadratic (productProbability t) from hmat,
    hmean,productProbability_mass,productProbability_mean]
  ring

theorem productGradientCorrection_decomposition {t : ℝ} (ht : -1<t) (ht1 : t<1) (j : Count) :
    gradient (productProbability t) j=
      (12*(Real.log (1+t)+Real.log (1-t))+2-2*quadratic (productProbability t)+
        2*productAffineCoefficient t*t)+
      (12*(Real.log (1+t)-Real.log (1-t))-2*productAffineCoefficient t)*meanCoordinate j-
      productGradientCorrection t j := by
  rw [gradient,productProbability_log_ratio ht ht1]
  unfold productGradientCorrection
  ring

theorem product_gibbs_lower (t : ℝ) (q : Count → ℝ)
    (ht : 0≤t) (ht1 : t<1) (hq : FeasibleAt t q) :
    functional (productProbability t)-(1/5)*Real.log
      (∑ j : Count,productProbability t j*Real.exp (5*productGradientCorrection t j))≤functional q := by
  apply functional_lower_of_gradient_decomposition (productProbability t) q (productGradientCorrection t)
    (12*(Real.log (1+t)+Real.log (1-t))+2-2*quadratic (productProbability t)+
      2*productAffineCoefficient t*t)
    (12*(Real.log (1+t)-Real.log (1-t))-2*productAffineCoefficient t)
    (productProbability_feasible ht ht1.le).1
    (productProbability_pos (by linarith) ht1) hq.1
  · rw [productProbability_mean,hq.2]
  · exact productGradientCorrection_decomposition (by linarith) ht1
  · exact productGradientCorrection_centered t

#print axioms product_gibbs_lower
end BecknerOnofri.HighDim.Spin

module

public import BecknerOnofri.SpinProductEntropy
public import BecknerOnofri.SpinProductMoments

@[expose] public section

/-! The exact product-law functional and the source's quartic baseline. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem productProbability_functional {t : ℝ} (ht : -1<t) (ht1 : t<1) :
    functional (productProbability t)=24*binaryCost t-
      ∑ s : Order,weight s*t^(2*(s.val+1)) := by
  rw [functional,productProbability_entropy ht ht1,productProbability_quadratic]
  ring

theorem product_quadratic_split (t : ℝ) :
    (∑ s : Order,weight s*t^(2*(s.val+1)))=
      12*t^2+∑ s : Order,if 2≤s.val+1 then weight s*t^(2*(s.val+1)) else 0 := by
  have he (s : Order) : weight s*t^(2*(s.val+1))=
      (if s=0 then 12*t^2 else 0)+(if 2≤s.val+1 then weight s*t^(2*(s.val+1)) else 0) := by
    by_cases hs : s=0
    · subst s
      norm_num [weight,weightQ]
    · have hs' : 2≤s.val+1 := by
        have hn : s.val≠0 := fun h => hs (Fin.ext h)
        omega
      simp [hs,hs']
  calc
    _ = ∑ s : Order,((if s=0 then 12*t^2 else 0)+
        (if 2≤s.val+1 then weight s*t^(2*(s.val+1)) else 0)) :=
      Finset.sum_congr rfl (fun s _ => he s)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem productProbability_quartic_baseline {t a : ℝ}
    (ht : 0≤t) (hta : t≤a) (ha : a<1) :
    (2-(∑ s : Order,if 2≤s.val+1 then weight s*a^(2*(s.val+1)-4) else 0))*t^4 ≤
      functional (productProbability t) := by
  have ht1 : t<1 := hta.trans_lt ha
  have hh : (∑ s : Order,if 2≤s.val+1 then weight s*t^(2*(s.val+1)) else 0)≤
      (∑ s : Order,if 2≤s.val+1 then weight s*a^(2*(s.val+1)-4) else 0)*t^4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : 2≤s.val+1
    · simp only [if_pos hs]
      have he : t^(2*(s.val+1))=t^(2*(s.val+1)-4)*t^4 := by
        rw [← pow_add]
        congr 1
        omega
      rw [he]
      have hpow := pow_le_pow_left₀ ht hta (2*(s.val+1)-4)
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (pow_nonneg ht 4))
        (weight_nonneg s)
      nlinarith
    · simp [hs]
  rw [productProbability_functional (by linarith) ht1,product_quadratic_split]
  have hB := binaryCost_quartic_lower ht ht1.le
  nlinarith

#print axioms productProbability_quartic_baseline
end BecknerOnofri.HighDim.Spin

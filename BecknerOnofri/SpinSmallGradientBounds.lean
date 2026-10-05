module

public import BecknerOnofri.SpinSmallVariancePolynomial

@[expose] public section

/-! Exact interval bounds on the actual nonaffine gradient. These imply the
manuscript's V0/O0 bounds, using a direct polynomial verification of the same
finite-state moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def smallFactorEnvelopeQ (j : Count) : ℚ :=
  2*∑ l : Fin 11,weightQ l.succ*(|momentQ l.succ j| * (1/16:ℚ)^l.val+
    (l.val+1:ℚ)*(1/16:ℚ)^(2*l.val+2)+
    (l.val+2:ℚ)*|meanCoordinateQ j| * (1/16:ℚ)^(2*l.val+1))

theorem small_factor_envelope_bound : ∀ j : Count,smallFactorEnvelopeQ j≤483/100 := by
  decide +kernel

theorem smallGradientFactor_abs {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) (j : Count) :
    |smallGradientFactor t j|≤483/100 := by
  have hp (n : ℕ) : 0≤t^n := pow_nonneg ht n
  have hpow (n : ℕ) : t^n≤(1/16:ℝ)^n := pow_le_pow_left₀ ht ht1 n
  have hj (l : Fin 11) :
      |weight l.succ*(moment l.succ j*t^l.val+
        (l.val+1:ℝ)*t^(2*l.val+2)-(l.val+2:ℝ)*meanCoordinate j*t^(2*l.val+1))|≤
      weight l.succ*(|moment l.succ j| * (1/16:ℝ)^l.val+
        (l.val+1:ℝ)*(1/16:ℝ)^(2*l.val+2)+
        (l.val+2:ℝ)*|meanCoordinate j| * (1/16:ℝ)^(2*l.val+1)) := by
    rw [abs_mul,abs_of_nonneg (weight_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg _)
    have ha := abs_add_le (moment l.succ j*t^l.val) ((l.val+1:ℝ)*t^(2*l.val+2))
    have hb := abs_sub (moment l.succ j*t^l.val+(l.val+1:ℝ)*t^(2*l.val+2))
      ((l.val+2:ℝ)*meanCoordinate j*t^(2*l.val+1))
    simp only [abs_mul,abs_of_nonneg (hp _),abs_of_nonneg (show 0≤(l.val+1:ℝ) by positivity),
      abs_of_nonneg (show 0≤(l.val+2:ℝ) by positivity)] at ha hb
    have hc := mul_le_mul_of_nonneg_left (hpow l.val) (abs_nonneg (moment l.succ j))
    have hd := mul_le_mul_of_nonneg_left (hpow (2*l.val+2)) (show 0≤(l.val+1:ℝ) by positivity)
    have he := mul_le_mul_of_nonneg_left (hpow (2*l.val+1))
      (show 0≤(l.val+2:ℝ)*|meanCoordinate j| by positivity)
    linarith
  have hs := (Finset.abs_sum_le_sum_abs (s:=Finset.univ)
    (f:=fun l : Fin 11 => weight l.succ*(moment l.succ j*t^l.val+
      (l.val+1:ℝ)*t^(2*l.val+2)-(l.val+2:ℝ)*meanCoordinate j*t^(2*l.val+1)))).trans
      (Finset.sum_le_sum (fun l _ => hj l))
  have he : (smallFactorEnvelopeQ j:ℝ)=
      2*∑ l : Fin 11,weight l.succ*(|moment l.succ j| * (1/16:ℝ)^l.val+
        (l.val+1:ℝ)*(1/16:ℝ)^(2*l.val+2)+
        (l.val+2:ℝ)*|meanCoordinate j| * (1/16:ℝ)^(2*l.val+1)) := by
    simp [smallFactorEnvelopeQ,weight,moment,meanCoordinate]
  have hc := Rat.cast_le (K:=ℝ).mpr (small_factor_envelope_bound j)
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hc
  rw [he] at hc
  unfold smallGradientFactor
  rw [abs_mul]
  norm_num
  linarith

theorem smallGradientFactor_variance {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) :
    (∑ j : Count,productProbability t j*(smallGradientFactor t j)^2)≤13/50 := by
  rw [small_variance_polynomial]
  have hj (n : Fin 23) : (smallVarianceCoefficientQ n:ℝ)*t^(2*n.val)≤
      (max (smallVarianceCoefficientQ n) 0:ℚ)*(1/16:ℝ)^(2*n.val) := by
    by_cases hc : 0≤smallVarianceCoefficientQ n
    · rw [max_eq_left hc]
      apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht ht1 _)
      exact_mod_cast hc
    · rw [max_eq_right (le_of_not_ge hc)]
      norm_num
      apply mul_nonpos_of_nonpos_of_nonneg _ (pow_nonneg ht _)
      exact_mod_cast (le_of_not_ge hc)
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ (Finset.univ : Finset (Fin 23))) => hj n)
  have hc := Rat.cast_le (K:=ℝ).mpr small_variance_coefficient_bound
  push_cast at hc hs
  exact hs.trans hc

theorem productGradientCorrection_small_bounds {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) :
    (∀ j,|productGradientCorrection t j|≤5*t^2) ∧
    (∑ j : Count,productProbability t j*(productGradientCorrection t j)^2)≤(13/50)*t^4 := by
  constructor
  · intro j
    rw [productGradientCorrection_factor,abs_mul,abs_of_nonneg (sq_nonneg t)]
    nlinarith [smallGradientFactor_abs ht ht1 j]
  · have he : (∑ j : Count,productProbability t j*(productGradientCorrection t j)^2)=
        t^4*(∑ j : Count,productProbability t j*(smallGradientFactor t j)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [productGradientCorrection_factor]
      ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left (smallGradientFactor_variance ht ht1) (pow_nonneg ht 4)
    nlinarith

/-- The same V0/O0 estimates as in the manuscript, obtained by exact
polynomial arithmetic on the thirteen-state law. -/
theorem productGradientCorrection_source_bounds {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) :
    (∀ i j,|productGradientCorrection t i-productGradientCorrection t j|≤
      (oscillationConstantQ:ℝ)*t^2) ∧
    (∑ j : Count,productProbability t j*(productGradientCorrection t j)^2)≤
      (varianceConstantQ:ℝ)*t^4 := by
  have hc : (483/50:ℚ)≤oscillationConstantQ ∧ (13/50:ℚ)≤varianceConstantQ := by decide +kernel
  have hO := Rat.cast_le (K:=ℝ).mpr hc.1
  have hV := Rat.cast_le (K:=ℝ).mpr hc.2
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hO hV
  constructor
  · intro i j
    have hi := smallGradientFactor_abs ht ht1 i
    have hj := smallGradientFactor_abs ht ht1 j
    have hd := abs_sub (smallGradientFactor t i) (smallGradientFactor t j)
    have hbound : |smallGradientFactor t i-smallGradientFactor t j|≤483/50 := by linarith
    rw [productGradientCorrection_factor,productGradientCorrection_factor,← mul_sub,
      abs_mul,abs_of_nonneg (sq_nonneg t)]
    have h := mul_le_mul_of_nonneg_left (hbound.trans hO) (sq_nonneg t)
    nlinarith
  · have h := (productGradientCorrection_small_bounds ht ht1).2
    have h' := mul_le_mul_of_nonneg_right hV (pow_nonneg ht 4)
    exact h.trans h'

#print axioms productGradientCorrection_small_bounds
#print axioms productGradientCorrection_source_bounds
end BecknerOnofri.HighDim.Spin

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

/-! Sound real-arithmetic quadrature rules for the dimension-twelve radial
partition calculation. These are exact integral inequalities, not a numerical
certificate or an assertion of the unproved partition bound. The heat rule
retains negative contributions and rounds their positive weights downward. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialQuadrature

/-- General nonnegative-weight interval bound; the upper function value may be negative. -/
theorem weighted_interval_upper {a b U : ℝ} (hab : a≤b) (w f : ℝ → ℝ)
    (hw : IntervalIntegrable w volume a b)
    (hf : IntervalIntegrable (fun t => w t*f t) volume a b)
    (hw0 : ∀ t ∈ Icc a b, 0≤w t) (hfU : ∀ t ∈ Icc a b, f t≤U) :
    (∫ t in a..b, w t*f t) ≤ (∫ t in a..b, w t)*U := by
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_mono_on hab hf (hw.mul_const U)
    (fun t ht => mul_le_mul_of_nonneg_left (hfU t ht) (hw0 t ht))

/-- Positive quadrature weights are rounded up for a nonnegative upper value,
and down for a negative upper value. This conditional is essential. -/
def roundedProduct (lowerWeight upperWeight upperValue : ℝ) : ℝ :=
  (if 0≤upperValue then upperWeight else lowerWeight)*upperValue

theorem mul_le_roundedProduct {W L H U : ℝ} (hL : L≤W) (hH : W≤H) :
    W*U≤roundedProduct L H U := by
  unfold roundedProduct
  split_ifs with hU
  · exact mul_le_mul_of_nonneg_right hH hU
  · exact mul_le_mul_of_nonpos_right hL (le_of_not_ge hU)

/-- Source (section5-signed-heat-subinterval), with s=6 and exact Gamma(6)=120. -/
theorem signed_heat_subinterval {a b U : ℝ} (ha : 0≤a) (hab : a≤b) (f : ℝ → ℝ)
    (hf : IntervalIntegrable (fun t => t^5*f t) volume a b)
    (hU : ∀ t ∈ Icc a b, f t≤U) :
    (1/Real.Gamma 6)*(∫ t in a..b, t^5*f t) ≤ ((b^6-a^6)/720)*U := by
  have hg : Real.Gamma 6=120 := by
    convert Real.Gamma_nat_eq_factorial 5 using 1 <;> norm_num
  have hh := weighted_interval_upper hab (fun t => t^5) f
    ((continuous_id.pow 5).intervalIntegrable a b) hf
    (fun t ht => pow_nonneg (ha.trans ht.1) 5) hU
  rw [integral_pow] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/120)
  rw [hg]
  convert! hh' using 1 <;> norm_num <;> ring

/-- Outward-rounded version of the exact signed heat rule. -/
theorem signed_heat_subinterval_rounded {a b U L H : ℝ} (ha : 0≤a) (hab : a≤b)
    (f : ℝ → ℝ) (hf : IntervalIntegrable (fun t => t^5*f t) volume a b)
    (hU : ∀ t ∈ Icc a b, f t≤U)
    (hL : L≤(b^6-a^6)/720) (hH : (b^6-a^6)/720≤H) :
    (1/Real.Gamma 6)*(∫ t in a..b, t^5*f t) ≤ roundedProduct L H U :=
  (signed_heat_subinterval ha hab f hf hU).trans (mul_le_roundedProduct hL hH)

/-- The exact radial weight in dimension twelve. -/
def radialWeight (S : ℝ) : ℝ := S^5/Real.sqrt (1-S)

theorem radialWeight_nonneg {S : ℝ} (hS : 0≤S) : 0≤radialWeight S :=
  div_nonneg (pow_nonneg hS 5) (Real.sqrt_nonneg _)

/-- Source (section5-radial-subinterval). Monotonicity is required of the
actual kernel K, while R is only a single certified upper bound at a. -/
theorem radial_subinterval {a b R : ℝ} (ha : 0≤a) (hab : a≤b) (K : ℝ → ℝ)
    (hK : AntitoneOn K (Icc a b)) (hR : K a≤R)
    (hw : IntervalIntegrable radialWeight volume a b)
    (hf : IntervalIntegrable (fun S => radialWeight S*Real.exp ((7/10)*K S)) volume a b) :
    (∫ S in a..b, radialWeight S*Real.exp ((7/10)*K S)) ≤
      Real.exp ((7/10)*R)*(∫ S in a..b, radialWeight S) := by
  rw [mul_comm (Real.exp _)]
  apply weighted_interval_upper hab radialWeight _ hw hf
    (fun S hS => radialWeight_nonneg (ha.trans hS.1))
  intro S hS
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left ((hK ⟨le_rfl,hab⟩ hS hS.1).trans hR) (by norm_num)

theorem radialWeight_continuousOn {a b : ℝ} (hab : a≤b) (hb : b<1) :
    ContinuousOn radialWeight (Icc a b) := by
  apply (continuous_id.pow 5).continuousOn.div
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn
  intro S hS
  exact (Real.sqrt_pos.mpr (by linarith [hS.2] : 0<1-S)).ne'

/-- Explicit analytic weight bound used on each geometric radial interval. -/
theorem radial_weight_integral_le {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b<1) :
    (∫ S in a..b, radialWeight S) ≤ (b^6-a^6)/(6*Real.sqrt (1-b)) := by
  have hw : IntervalIntegrable radialWeight volume a b :=
    ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le hab] using radialWeight_continuousOn hab hb)
  have hg : IntervalIntegrable (fun S : ℝ => S^5/Real.sqrt (1-b)) volume a b :=
    ((continuous_id.pow 5).div_const _).intervalIntegrable a b
  have hh : (∫ S in a..b, radialWeight S) ≤ ∫ S in a..b, S^5/Real.sqrt (1-b) := by
    apply intervalIntegral.integral_mono_on hab hw hg
    intro S hS
    exact div_le_div_of_nonneg_left (pow_nonneg (ha.trans hS.1) 5)
      (Real.sqrt_pos.mpr (by linarith : 0<1-b)) (Real.sqrt_le_sqrt (by linarith [hS.2]))
  rw [intervalIntegral.integral_div,integral_pow] at hh
  convert hh using 1 <;> ring

/-- Fully explicit geometric-interval contribution bound from the source. -/
theorem radial_subinterval_explicit {a b R : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b<1)
    (K : ℝ → ℝ) (hK : AntitoneOn K (Icc a b)) (hR : K a≤R)
    (hf : IntervalIntegrable (fun S => radialWeight S*Real.exp ((7/10)*K S)) volume a b) :
    (∫ S in a..b, radialWeight S*Real.exp ((7/10)*K S)) ≤
      Real.exp ((7/10)*R)*(b^6-a^6)/(6*Real.sqrt (1-b)) := by
  have hw : IntervalIntegrable radialWeight volume a b :=
    ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le hab] using radialWeight_continuousOn hab hb)
  have h1 := radial_subinterval ha hab K hK hR hw hf
  have h2 := mul_le_mul_of_nonneg_left (radial_weight_integral_le ha hab hb) (Real.exp_pos ((7/10)*R)).le
  simpa only [mul_div_assoc] using h1.trans h2

/-- Exact rational polynomial primitive after S=1-v²; no endpoint singularity remains. -/
def endpointPrimitive (v : ℝ) : ℝ :=
  2*v-(10/3)*v^3+4*v^5-(20/7)*v^7+(10/9)*v^9-(2/11)*v^11

theorem endpointPrimitive_hasDerivAt (v : ℝ) :
    HasDerivAt endpointPrimitive (2*(1-v^2)^5) v := by
  have hh := ((((((hasDerivAt_id v).const_mul 2).sub
    ((hasDerivAt_pow 3 v).const_mul (10/3))).add
    ((hasDerivAt_pow 5 v).const_mul 4)).sub
    ((hasDerivAt_pow 7 v).const_mul (20/7))).add
    ((hasDerivAt_pow 9 v).const_mul (10/9))).sub
    ((hasDerivAt_pow 11 v).const_mul (2/11))
  convert! hh using 1 <;> ring

theorem endpoint_weight_integral (a b : ℝ) :
    (∫ v in a..b, 2*(1-v^2)^5)=endpointPrimitive b-endpointPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => endpointPrimitive_hasDerivAt v)
  exact (continuous_const.mul ((continuous_const.sub (continuous_id.pow 2)).pow 5)).intervalIntegrable a b

/-- Exact transformed endpoint-interval rule used for the 2048 dyadic v-bins. -/
theorem endpoint_subinterval {a b R : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (K : ℝ → ℝ) (hK : AntitoneOn K (Icc (1-b^2) (1-a^2))) (hR : K (1-b^2)≤R)
    (hf : IntervalIntegrable (fun v => 2*(1-v^2)^5*Real.exp ((7/10)*K (1-v^2))) volume a b) :
    (∫ v in a..b, 2*(1-v^2)^5*Real.exp ((7/10)*K (1-v^2))) ≤
      Real.exp ((7/10)*R)*(endpointPrimitive b-endpointPrimitive a) := by
  have hw : IntervalIntegrable (fun v : ℝ => 2*(1-v^2)^5) volume a b :=
    (continuous_const.mul ((continuous_const.sub (continuous_id.pow 2)).pow 5)).intervalIntegrable a b
  have hn : ∀ v∈Icc a b, 0≤2*(1-v^2)^5 := by
    intro v hv
    have hv0 : 0≤v := ha.trans hv.1
    have hv1 : v≤1 := hv.2.trans hb
    have hh : 0≤1-v^2 := by nlinarith
    positivity
  have he : ∀ v∈Icc a b, Real.exp ((7/10)*K (1-v^2))≤Real.exp ((7/10)*R) := by
    intro v hv
    have hv0 : 0≤v := ha.trans hv.1
    have hb0 : 0≤b := ha.trans hab
    have hl : 1-b^2≤1-v^2 := by nlinarith [pow_le_pow_left₀ hv0 hv.2 2]
    have hr : 1-v^2≤1-a^2 := by nlinarith [pow_le_pow_left₀ ha hv.1 2]
    have hba : 1-b^2≤1-a^2 := hl.trans hr
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((hK ⟨le_rfl,hba⟩ ⟨hl,hr⟩ hl).trans hR) (by norm_num)
  have hh := weighted_interval_upper hab _ _ hw hf hn he
  rw [endpoint_weight_integral] at hh
  simpa only [mul_comm] using hh

/-- Exact summation of finite interval upper bounds, including signed contributions. -/
theorem finite_interval_upper {n : ℕ} (a : ℕ → ℝ) (f : ℝ → ℝ) (B : ℕ → ℝ)
    (hf : ∀ i<n, IntervalIntegrable f volume (a i) (a (i+1)))
    (hB : ∀ i<n, (∫ t in a i..a (i+1), f t)≤B i) :
    (∫ t in a 0..a n, f t) ≤ ∑ i ∈ Finset.range n, B i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hf]
  exact Finset.sum_le_sum (fun i hi => hB i (Finset.mem_range.mp hi))

#print axioms endpoint_subinterval
#print axioms signed_heat_subinterval_rounded
#print axioms radial_subinterval_explicit
#print axioms finite_interval_upper
end BecknerOnofri.HighDim.RadialQuadrature

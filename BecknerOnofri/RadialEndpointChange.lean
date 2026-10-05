module

public import BecknerOnofri.RadialMeasure
public import BecknerOnofri.RadialQuadrature

@[expose] public section

/-! The actual endpoint substitution removes the square-root singularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialSeedReduction
open RadialQuadrature

def endpointMap (v : ℝ) : ℝ := 1-v^2

theorem endpoint_image : endpointMap '' Ioo (0:ℝ) (3/4) = Ioo (7/16:ℝ) 1 := by
  ext S
  constructor
  · rintro ⟨v,hv,rfl⟩
    dsimp [endpointMap]
    constructor <;> nlinarith [hv.1,hv.2]
  · intro hS
    refine ⟨Real.sqrt (1-S),⟨Real.sqrt_pos.mpr (by linarith [hS.2]),?_⟩,?_⟩
    · apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<3/4)).mpr
      nlinarith [hS.1]
    · rw [endpointMap,Real.sq_sqrt (by linarith [hS.2])]
      ring

theorem endpoint_injOn : InjOn endpointMap (Ioo (0:ℝ) (3/4)) := by
  intro x hx y hy he
  dsimp [endpointMap] at he
  nlinarith [hx.1,hy.1]

theorem endpoint_derivative (v : ℝ) : HasDerivAt endpointMap (-2*v) v := by
  convert! ((hasDerivAt_pow 2 v).const_sub 1) using 1 <;> simp [endpointMap] <;> ring

theorem endpoint_weight_identity {v : ℝ} (hv : v∈Ioo (0:ℝ) (3/4)) (K : ℝ → ℝ) :
    |(-2:ℝ)*v| * (radialWeight (endpointMap v)*Real.exp ((7/10:ℝ)*K (endpointMap v))) =
      2*(1-v^2)^5*Real.exp ((7/10:ℝ)*K (1-v^2)) := by
  have hv0 : 0 < v := hv.1
  simp only [radialWeight,endpointMap,show 1-(1-v^2)=v^2 by ring,Real.sqrt_sq_eq_abs,
    abs_of_pos hv0,abs_mul,abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  field_simp

/-- Exact substitution, including the singular endpoint as an a.e.-irrelevant point. -/
theorem endpoint_integral_change (K : ℝ → ℝ) :
    (∫ S in (7/16:ℝ)..1,radialWeight S*Real.exp ((7/10:ℝ)*K S)) =
      ∫ v in (0:ℝ)..(3/4),2*(1-v^2)^5*Real.exp ((7/10:ℝ)*K (1-v^2)) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (7/16:ℝ)≤1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤3/4),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  rw [← endpoint_image]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun v _ => (endpoint_derivative v).hasDerivWithinAt) endpoint_injOn]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  exact endpoint_weight_identity hv K

/-- Measurability and exact radial monotonicity already imply integrability
of the transformed endpoint integral; no analytic integrability premise remains. -/
theorem endpoint_transformed_integrable (K : ℝ → ℝ) (hK : Measurable K)
    (hanti : AntitoneOn K (Ioc (0:ℝ) 12)) :
    IntervalIntegrable (fun v => 2*(1-v^2)^5*Real.exp ((7/10:ℝ)*K (1-v^2))) volume 0 (3/4) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤3/4)).mpr
  have hc : IntegrableOn (fun _ : ℝ => 2*Real.exp ((7/10:ℝ)*K (7/16))) (Ioc (0:ℝ) (3/4)) := integrable_const _
  refine hc.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hr : (7/16:ℝ) ≤ 1-v^2 := by nlinarith [hv.1,hv.2]
  have hr1 : 1-v^2 ≤ 1 := by nlinarith [sq_nonneg v]
  have hp : 0 ≤ 2*(1-v^2)^5*Real.exp ((7/10:ℝ)*K (1-v^2)) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hp]
  have hex : Real.exp ((7/10:ℝ)*K (1-v^2)) ≤ Real.exp ((7/10:ℝ)*K (7/16)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hanti (by constructor <;> norm_num)
      ⟨by linarith,by linarith⟩ hr) (by norm_num)
  have hpow : (1-v^2)^5 ≤ 1 := by
    simpa using pow_le_pow_left₀ (by linarith : 0 ≤ 1-v^2) hr1 5
  exact (mul_le_mul_of_nonneg_left hex (by positivity)).trans
    (by nlinarith [Real.exp_pos ((7/10:ℝ)*K (7/16))])

theorem endpoint_radial_integrable (K : ℝ → ℝ) (hK : Measurable K)
    (hanti : AntitoneOn K (Ioc (0:ℝ) 12)) :
    IntervalIntegrable (fun S => radialWeight S*Real.exp ((7/10:ℝ)*K S)) volume (7/16) 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (7/16:ℝ)≤1)).mpr
  rw [integrableOn_Ioc_iff_integrableOn_Ioo,← endpoint_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun v _ => (endpoint_derivative v).hasDerivWithinAt) endpoint_injOn]
  have h := (endpoint_transformed_integrable K hK hanti).1.mono_set Ioo_subset_Ioc_self
  apply h.congr_fun (fun v hv => ?_) measurableSet_Ioo
  exact (endpoint_weight_identity hv K).symm

#print axioms endpoint_radial_integrable

#print axioms endpoint_integral_change
#print axioms endpoint_transformed_integrable
end BecknerOnofri.HighDim.RadialSeedReduction

module

public import BecknerOnofri.RadialE1Euler
public import BecknerOnofri.SpatialThetaDiagonal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import BecknerOnofri.RadialQuadrature

@[expose] public section

/-! Exact bounds for the singular origin contribution in the radial seed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology
namespace BecknerOnofri.HighDim.RadialOrigin
open SpatialThetaDiagonal

theorem arcsin_le_four_thirds {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) :
    Real.arcsin x≤(4/3:ℝ)*x := by
  have hder (y : ℝ) (hy : y∈Icc (0:ℝ) (1/2)) :
      HasDerivWithinAt Real.arcsin (1/Real.sqrt (1-y^2)) (Icc (0:ℝ) (1/2)) y :=
    (Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])).hasDerivWithinAt
  have hbound (y : ℝ) (hy : y∈Icc (0:ℝ) (1/2)) : ‖1/Real.sqrt (1-y^2)‖≤(4/3:ℝ) := by
    have hp : 0<1-y^2 := by nlinarith [hy.1,hy.2]
    have hsq := Real.sq_sqrt hp.le
    have hs := Real.sqrt_nonneg (1-y^2)
    rw [Real.norm_eq_abs,abs_of_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hp)),
      div_le_iff₀ (Real.sqrt_pos.mpr hp)]
    nlinarith [hy.1,hy.2,sq_nonneg (y-1/2)]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_Icc (0:ℝ) (1/2)) (show (0:ℝ)∈Icc (0:ℝ) (1/2) by constructor <;> norm_num) hx
  rw [Real.arcsin_zero,sub_zero,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx.1,
    abs_of_nonneg (Real.arcsin_nonneg.mpr hx.1)] at hh
  exact hh

theorem square_argument_identity (S : ℝ) :
    Real.pi^2*12*(radialAngle 12 S)^2=12*(Real.arcsin (Real.sqrt (S/12)))^2 := by
  unfold radialAngle
  norm_num only [Nat.cast_ofNat]
  field_simp

theorem small_argument_comparison {S : ℝ} (hS : S∈Icc (0:ℝ) 1) :
    S≤Real.pi^2*12*(radialAngle 12 S)^2 ∧ Real.pi^2*12*(radialAngle 12 S)^2≤2*S := by
  rw [square_argument_identity]
  have hsqrt : Real.sqrt (S/12)∈Icc (0:ℝ) (1/2) := by
    refine ⟨Real.sqrt_nonneg _,?_⟩
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith [hS.1,hS.2]
  have hsquare := Real.sq_sqrt (div_nonneg hS.1 (by norm_num) : 0≤S/12)
  have hu := arcsin_le_four_thirds hsqrt
  have hnonneg := Real.arcsin_nonneg.mpr hsqrt.1
  have hsin : Real.sin (Real.arcsin (Real.sqrt (S/12)))=Real.sqrt (S/12) :=
    Real.sin_arcsin (by linarith [hsqrt.1]) (by linarith [hsqrt.2])
  have hl : Real.sqrt (S/12)≤Real.arcsin (Real.sqrt (S/12)) := by
    simpa only [hsin] using Real.sin_le (Real.arcsin_nonneg.mpr hsqrt.1)
  constructor
  · nlinarith [mul_self_le_mul_self hsqrt.1 hl]
  · have hh := mul_self_le_mul_self hnonneg hu
    nlinarith

/-- Exact source estimate for the singular n=0 Poisson image. -/
theorem origin_E1_bound {S S₀ : ℝ} (hS : 0<S) (hSS : S≤S₀) (hS₀ : S₀≤1) :
    RadialE1.E1 (Real.pi^2*12*(radialAngle 12 S)^2)≤
      -(5771/10000:ℝ)-Real.log S+2*S₀ := by
  have hz := small_argument_comparison ⟨hS.le,hSS.trans hS₀⟩
  have he := RadialE1.rational_logarithmic_bound (hS.trans_le hz.1)
  have hl := Real.log_le_log hS hz.1
  linarith [hz.2]

/-- The exponential of a logarithmic majorant is an exact power majorant. -/
theorem logarithmic_exponential_identity {S : ℝ} (hS : 0<S) (C c : ℝ) :
    S^5*Real.exp ((7/10:ℝ)*(C-c*Real.log S))=
      Real.exp ((7/10:ℝ)*C)*S^((5:ℝ)-(7/10:ℝ)*c) := by
  have he : S^5=Real.exp ((5:ℝ)*Real.log S) := by
    rw [show (5:ℝ)=((5:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hS]
  rw [he,Real.rpow_def_of_pos hS,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

/-- The entire singular interval is integrated analytically with its true power. -/
theorem origin_integral_bound {S₀ C c : ℝ} (hS₀ : 0<S₀) (hS₀' : S₀<1)
    (hp : 0<(6:ℝ)-(7/10:ℝ)*c) (K : ℝ → ℝ)
    (hK : ∀ S∈Ioc (0:ℝ) S₀,K S≤C-c*Real.log S)
    (hf : IntervalIntegrable (fun S => RadialQuadrature.radialWeight S*Real.exp ((7/10:ℝ)*K S)) volume 0 S₀) :
    (∫ S in 0..S₀,RadialQuadrature.radialWeight S*Real.exp ((7/10:ℝ)*K S))≤
      Real.exp ((7/10:ℝ)*C)*S₀^((6:ℝ)-(7/10:ℝ)*c)/
        (((6:ℝ)-(7/10:ℝ)*c)*Real.sqrt (1-S₀)) := by
  let p := (5:ℝ)-(7/10:ℝ)*c
  have hp' : -1<p := by dsimp [p]; linarith
  have hpow : IntervalIntegrable (fun S : ℝ => S^p) volume 0 S₀ :=
    intervalIntegral.intervalIntegrable_rpow' hp'
  have hg := (hpow.const_mul (Real.exp ((7/10:ℝ)*C))).div_const (Real.sqrt (1-S₀))
  have hh : (∫ S in 0..S₀,RadialQuadrature.radialWeight S*Real.exp ((7/10:ℝ)*K S))≤
      ∫ S in 0..S₀,Real.exp ((7/10:ℝ)*C)*S^p/Real.sqrt (1-S₀) := by
    simp only [intervalIntegral.integral_of_le hS₀.le]
    apply setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc
    intro S hS
    have hd : 0<Real.sqrt (1-S) := Real.sqrt_pos.mpr (by linarith [hS.2])
    have hd₀ : 0<Real.sqrt (1-S₀) := Real.sqrt_pos.mpr (by linarith)
    calc
      _ ≤ (S^5*Real.exp ((7/10:ℝ)*(C-c*Real.log S)))/Real.sqrt (1-S) := by
        unfold RadialQuadrature.radialWeight
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hd.le
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hS.1.le 5)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (hK S hS) (by norm_num : (0:ℝ)≤7/10)
      _ = Real.exp ((7/10:ℝ)*C)*S^p/Real.sqrt (1-S) := by rw [logarithmic_exponential_identity hS.1]
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hS.1.le _)) hd₀ (Real.sqrt_le_sqrt (by linarith [hS.2]))
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hp'),Real.zero_rpow (by linarith : p+1≠0),sub_zero] at hh
  have hpeq : p+1=(6:ℝ)-(7/10:ℝ)*c := by dsimp [p]; ring
  rw [hpeq] at hh
  simpa only [← mul_div_assoc,div_div] using hh

#print axioms origin_E1_bound
#print axioms origin_integral_bound
end BecknerOnofri.HighDim.RadialOrigin

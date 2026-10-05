module

public import BecknerOnofri.SpatialThetaJacobiProducts

@[expose] public section

/-! The actual product's Fourier recurrence identifies its spectrum with the
spatial Gaussian theta spectrum, up to one common normalization constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SpatialThetaJacobi

def gaussianWeight (t : ℝ) (n : ℤ) : ℂ := Real.exp (-t*(n:ℝ)^2)

theorem gaussianWeight_ne_zero (t : ℝ) (n : ℤ) : gaussianWeight t n≠0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

theorem gaussianWeight_succ (t : ℝ) (n : ℤ) :
    gaussianWeight t (n+1)=(Real.exp (-t):ℂ)*(Real.exp (-2*t):ℂ)^n*gaussianWeight t n := by
  simp only [gaussianWeight,Complex.ofReal_exp,← Complex.exp_int_mul,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The genuine Banach product's coefficient recursion. -/
theorem coefficient_paired_succ {t : ℝ} (ht : 0<t) (n : ℤ) :
    coefficient (n+1) (pairedProduct t 1)=
      (Real.exp (-t):ℂ)*(Real.exp (-2*t):ℂ)^n*coefficient n (pairedProduct t 1) := by
  have hq : (Real.exp (-t):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hb : (Real.exp (-2*t):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hh := coefficient_paired_scaling ht (Real.exp (-2*t):ℂ) hb n
  rw [pairedProduct_shift ht,map_smul,coefficient_mul_fourier] at hh
  have hh' := congrArg (fun z : ℂ => (Real.exp (-t):ℂ)*z) hh
  simpa only [smul_eq_mul,sub_neg_eq_add,mul_assoc,mul_inv_cancel_left₀ hq] using hh'

/-- All integer coefficients have the actual Gaussian shape. The periodic
quotient argument treats positive and negative frequencies together. -/
theorem coefficient_paired_gaussian {t : ℝ} (ht : 0<t) (n : ℤ) :
    coefficient n (pairedProduct t 1)=gaussianWeight t n*coefficient 0 (pairedProduct t 1) := by
  let D : ℤ → ℂ := fun k => coefficient k (pairedProduct t 1)/gaussianWeight t k
  have hq : (Real.exp (-t):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hb : (Real.exp (-2*t):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hperiod : Function.Periodic D 1 := by
    intro k
    dsimp [D]
    rw [coefficient_paired_succ ht,gaussianWeight_succ]
    field_simp [hq,hb,gaussianWeight_ne_zero]
  have hh := hperiod.int_mul_eq n
  have hh' : coefficient n (pairedProduct t 1)/gaussianWeight t n=
      coefficient 0 (pairedProduct t 1) := by
    simpa only [Int.cast_id,mul_one,D,gaussianWeight,Int.cast_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      mul_zero,Real.exp_zero,Complex.ofReal_one,div_one] using hh
  exact (div_eq_iff (gaussianWeight_ne_zero t n)).mp hh' |>.trans (mul_comm _ _)

def thetaMap (t : ℝ) : Space := ∑' n : ℤ, gaussianWeight t n • fourier n

theorem thetaMap_summable {t : ℝ} (ht : 0<t) :
    Summable (fun n : ℤ => (gaussianWeight t n • fourier n : Space)) := by
  have hs : Summable (fun n : ℤ => Real.exp (-t*(n:ℝ)^2)) := by
    simpa only [zero_mul,add_zero] using
      Legacy.TorusEndpoint.TorusHeatPositivity.gaussian_quadratic_summable ht 0
  apply hs.of_norm_bounded
  intro n
  simp only [norm_smul,fourier_norm,mul_one,gaussianWeight,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),le_refl]

theorem thetaMap_apply {t : ℝ} (ht : 0<t) (x : UnitAddCircle) :
    thetaMap t x=Legacy.TorusEndpoint.TorusHeatPositivity.theta (t/Real.pi) x := by
  change (ContinuousMap.evalCLM ℂ x) (∑' n : ℤ, gaussianWeight t n • fourier n)=_
  rw [(ContinuousMap.evalCLM ℂ x).map_tsum (thetaMap_summable ht)]
  apply tsum_congr
  intro n
  change (Real.exp (-t*(n:ℝ)^2):ℂ)*fourier n x=
    (Real.exp (-Real.pi*(t/Real.pi)*(n:ℝ)^2):ℂ)*fourier n x
  congr 3
  field_simp

theorem coefficient_thetaMap {t : ℝ} (ht : 0<t) (n : ℤ) :
    coefficient n (thetaMap t)=gaussianWeight t n := by
  rw [thetaMap,(coefficient n).map_tsum (thetaMap_summable ht)]
  simp only [map_smul,coefficient_fourier,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simpa only [eq_comm] using tsum_ite_eq n (gaussianWeight t)

/-- Actual equality of continuous circle functions, from complete Fourier
coefficient uniqueness and the rigorously obtained recursion. -/
theorem pairedProduct_eq_theta {t : ℝ} (ht : 0<t) :
    pairedProduct t 1=coefficient 0 (pairedProduct t 1) • thetaMap t := by
  apply coefficient_ext
  intro n
  rw [map_smul,coefficient_thetaMap ht,coefficient_paired_gaussian ht]
  exact mul_comm _ _

#print axioms coefficient_paired_gaussian
#print axioms pairedProduct_eq_theta
end BecknerOnofri.HighDim.SpatialThetaJacobi

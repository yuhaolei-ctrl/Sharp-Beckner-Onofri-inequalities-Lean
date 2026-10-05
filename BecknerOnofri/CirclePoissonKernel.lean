import BecknerOnofri.CirclePoissonDefinitions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

theorem denominator_pos (q : ℝ) (hq : 0≤q) (hq1 : q<1) (x : UnitAddCircle) :
    0<1-2*q*(fourier 1 x).re+q^2 := by
  have hz : (fourier 1 x).re≤1 := by
    have h := Complex.re_le_norm (fourier 1 x)
    simpa only [fourier_apply,Circle.norm_coe] using h
  have hsq : 0<(1-q)^2 := sq_pos_of_pos (by linarith)
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hz)]

theorem kernel_pos (q : ℝ) (hq : 0≤q) (hq1 : q<1) (x : UnitAddCircle) :
    0<kernel q x := by
  apply div_pos _ (denominator_pos q hq hq1 x)
  nlinarith

theorem kernel_continuous (q : ℝ) (hq : 0≤q) (hq1 : q<1) : Continuous (kernel q) := by
  apply Continuous.div continuous_const
  · fun_prop
  · intro x; exact (denominator_pos q hq hq1 x).ne'

theorem fourier_nat (n : ℕ) (x : UnitAddCircle) :
    fourier (n:ℤ) x=(fourier 1 x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,pow_succ]

theorem series_summable (q : ℝ) (hq : 0≤q) (hq1 : q<1) (x : UnitAddCircle) :
    Summable (fun n : ℕ => q^n*(fourier (n:ℤ) x).re) := by
  have hn : ‖(q:ℂ)*fourier 1 x‖<1 := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq,
      fourier_apply,Circle.norm_coe,mul_one] using hq1
  have h := Complex.reCLM.hasSum (hasSum_geometric_of_norm_lt_one hn)
  simpa only [Complex.reCLM_apply,mul_pow,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,← fourier_nat] using h.summable

theorem kernel_series (q : ℝ) (hq : 0≤q) (hq1 : q<1) (x : UnitAddCircle) :
    kernel q x=2*(∑' n : ℕ,q^n*(fourier (n:ℤ) x).re)-1 := by
  have hn : ‖(q:ℂ)*fourier 1 x‖<1 := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq,
      fourier_apply,Circle.norm_coe,mul_one] using hq1
  have hs := (Complex.reCLM.hasSum (hasSum_geometric_of_norm_lt_one hn)).tsum_eq
  have he : (∑' n : ℕ,q^n*(fourier (n:ℤ) x).re)=((1-(q:ℂ)*fourier 1 x)⁻¹).re := by
    simpa only [Complex.reCLM_apply,mul_pow,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,← fourier_nat] using hs
  rw [he,Complex.inv_re]
  have hunit : (fourier 1 x).re^2+(fourier 1 x).im^2=1 := by
    have h : Complex.normSq (fourier 1 x)=1 := by simp [fourier_apply]
    simpa [Complex.normSq_apply,pow_two] using h
  have hnorm : Complex.normSq (1-(q:ℂ)*fourier 1 x)=1-2*q*(fourier 1 x).re+q^2 := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
      Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero]
    nlinarith [congrArg (fun v : ℝ => q^2*v) hunit]
  rw [hnorm]
  simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  unfold kernel
  let d := 1-2*q*(fourier 1 x).re+q^2
  have hd : d≠0 := (denominator_pos q hq hq1 x).ne'
  change (1-q^2)/d=2*((1-q*(fourier 1 x).re)/d)-1
  calc
    _ = (2*(1-q*(fourier 1 x).re)-d)/d := by dsimp [d]; congr 1; ring
    _ = _ := by rw [sub_div,div_self hd]; ring

#print axioms kernel_series
end BecknerOnofri.HighDim.CirclePoisson

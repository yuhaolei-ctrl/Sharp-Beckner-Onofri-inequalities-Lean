import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-! Three integrations by parts give weighted absolute Fourier summability.
The derivative chain and its endpoint equalities are explicit in this lemma. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleRegularity

theorem coefficient_derivative (f g : ℝ → ℂ) (hder : ∀ x,HasDerivAt f (g x) x)
    (hg : Continuous g) (hend : f 1=f 0) (n : ℤ) (hn : n≠0) :
    fourierCoeffOn (by norm_num : (0:ℝ)<1) f n=
      (2*(Real.pi:ℂ)*Complex.I*n)⁻¹*fourierCoeffOn (by norm_num : (0:ℝ)<1) g n := by
  have h := fourierCoeffOn_of_hasDerivAt (by norm_num : (0:ℝ)<1) hn
    (fun x _ => hder x) (hg.intervalIntegrable 0 1)
  rw [h]
  simp only [hend,sub_self,mul_zero,Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul,zero_sub,one_div]
  have he : (-2*(Real.pi:ℂ)*Complex.I*n)= -(2*(Real.pi:ℂ)*Complex.I*n) := by ring
  rw [he,inv_neg,neg_mul_neg]

theorem coefficient_norm_le (f : ℝ → ℂ) (C : ℝ)
    (hC : ∀ x ∈ Icc (0:ℝ) 1,‖f x‖≤C) (n : ℤ) :
    ‖fourierCoeffOn (by norm_num : (0:ℝ)<1) f n‖≤C := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero,one_div,inv_one,one_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=1) (C:=C)
    (f:=fun x : ℝ => fourier (-n) (x : UnitAddCircle)*f x) (fun x hx => by
      rw [norm_mul,show ‖fourier (-n) (x : UnitAddCircle)‖=1 by simp only [fourier_apply,Circle.norm_coe],one_mul]
      have hx' : x ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using hx
      exact hC x ⟨hx'.1.le,hx'.2⟩)
  simpa only [smul_eq_mul,sub_zero,abs_one,mul_one,fourier_coe_apply,Complex.ofReal_one,Complex.ofReal_sub,Complex.ofReal_zero,div_one] using h

theorem cubic_decay (f₀ f₁ f₂ f₃ : ℝ → ℂ)
    (h₀ : ∀ x,HasDerivAt f₀ (f₁ x) x) (h₁ : ∀ x,HasDerivAt f₁ (f₂ x) x)
    (h₂ : ∀ x,HasDerivAt f₂ (f₃ x) x)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (hc₃ : Continuous f₃)
    (he₀ : f₀ 1=f₀ 0) (he₁ : f₁ 1=f₁ 0) (he₂ : f₂ 1=f₂ 0)
    (C : ℝ) (hC : ∀ x ∈ Icc (0:ℝ) 1,‖f₃ x‖≤C) (n : ℤ) (hn : n≠0) :
    ‖fourierCoeffOn (by norm_num : (0:ℝ)<1) f₀ n‖≤C/(2*Real.pi*|(n:ℝ)|)^3 := by
  rw [coefficient_derivative f₀ f₁ h₀ hc₁ he₀ n hn,
    coefficient_derivative f₁ f₂ h₁ hc₂ he₁ n hn,
    coefficient_derivative f₂ f₃ h₂ hc₃ he₂ n hn]
  simp only [norm_mul,norm_inv,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_I,Complex.norm_intCast,mul_one]
  have hbound := coefficient_norm_le f₃ C hC n
  calc
    _ ≤ (2*Real.pi*|(n:ℝ)|)⁻¹*((2*Real.pi*|(n:ℝ)|)⁻¹*((2*Real.pi*|(n:ℝ)|)⁻¹*C)) := by
      gcongr
    _ = _ := by ring

theorem weighted_summable_of_cubic_decay (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n : ℤ,n ≠ 0 → ‖a n‖ ≤ C / |(n:ℝ)|^3) :
    Summable (fun n : ℤ => (1+|(n:ℝ)|)*‖a n‖) := by
  have hs : Summable (fun n : ℤ => 1 / (n:ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually (hs.mul_left (2*C))
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with n hn
  have hr : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
  calc
    (1+|(n:ℝ)|)*‖a n‖ ≤ (1+|(n:ℝ)|)*(C/|(n:ℝ)|^3) :=
      mul_le_mul_of_nonneg_left (ha n hn) (by positivity)
    _ ≤ (2*|(n:ℝ)|)*(C/|(n:ℝ)|^3) := by gcongr; linarith
    _ = 2*C*(1/(n:ℝ)^2) := by
      rw [← sq_abs (n:ℝ)]
      field_simp

theorem weighted_summable_of_derivative_chain (f₀ f₁ f₂ f₃ : ℝ → ℂ)
    (h₀ : ∀ x,HasDerivAt f₀ (f₁ x) x) (h₁ : ∀ x,HasDerivAt f₁ (f₂ x) x)
    (h₂ : ∀ x,HasDerivAt f₂ (f₃ x) x)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (hc₃ : Continuous f₃)
    (he₀ : f₀ 1=f₀ 0) (he₁ : f₁ 1=f₁ 0) (he₂ : f₂ 1=f₂ 0) :
    Summable (fun n : ℤ => (1+|(n:ℝ)|)*
      ‖fourierCoeffOn (by norm_num : (0:ℝ)<1) f₀ n‖) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn hc₃.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by norm_num))
  apply weighted_summable_of_cubic_decay _ (C/(2*Real.pi)^3) (by positivity)
  intro n hn
  have h := cubic_decay f₀ f₁ f₂ f₃ h₀ h₁ h₂ hc₁ hc₂ hc₃ he₀ he₁ he₂ C hC n hn
  simpa only [mul_pow,div_mul_eq_div_div] using h

theorem periodic_deriv (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  rw [← deriv_comp_add_const]
  have hfun : (fun x => f (x+1))=f := funext hf
  rw [hfun]

theorem weighted_summable_of_contDiff (f : ℝ → ℂ)
    (hf : ContDiff ℝ 3 f) (hp : Function.Periodic f 1) :
    Summable (fun n : ℤ => (1+|(n:ℝ)|)*
      ‖fourierCoeffOn (by norm_num : (0:ℝ)<1) f n‖) := by
  have hf₁ : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hf₂ : ContDiff ℝ 1 (deriv (deriv f)) := hf₁.deriv'
  have hf₃ : ContDiff ℝ 0 (deriv (deriv (deriv f))) := hf₂.deriv'
  have hp₁ := periodic_deriv f hp
  have hp₂ := periodic_deriv (deriv f) hp₁
  exact weighted_summable_of_derivative_chain f (deriv f) (deriv (deriv f))
    (deriv (deriv (deriv f)))
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hf₁.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hf₂.differentiable (by norm_num) x).hasDerivAt)
    hf₁.continuous hf₂.continuous hf₃.continuous
    (by simpa using hp 0) (by simpa using hp₁ 0) (by simpa using hp₂ 0)

#print axioms weighted_summable_of_contDiff
end BecknerOnofri.HighDim.CircleRegularity

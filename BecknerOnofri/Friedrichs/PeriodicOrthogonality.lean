module

public import BecknerOnofri.Friedrichs.PeriodicEigenprofiles
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs

lemma periodic_cos_integral (n : ℤ) :
    (∫ t in Ioc 0 (2*Real.pi),Real.cos ((n:ℝ)*t))=if n=0 then 2*Real.pi else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  by_cases hn : n=0
  · simp [hn]
  · rw [intervalIntegral.integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn),integral_cos]
    have hs : Real.sin ((n:ℝ)*(2*Real.pi))=0 := by simpa using Real.sin_periodic.int_mul_eq n
    simp [hn,hs]

lemma periodic_sin_integral (n : ℤ) :
    (∫ t in Ioc 0 (2*Real.pi),Real.sin ((n:ℝ)*t))=0 := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  by_cases hn : n=0
  · simp [hn]
  · rw [intervalIntegral.integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn),integral_sin]
    simp [Real.cos_int_mul_two_pi]

lemma periodic_cos_integrable (n : ℤ) :
    Integrable (fun t : ℝ => Real.cos ((n:ℝ)*t)) (volume.restrict (Ioc 0 (2*Real.pi))) :=
  (show Continuous (fun t : ℝ => Real.cos ((n:ℝ)*t)) by fun_prop).integrableOn_Ioc

lemma periodic_sin_integrable (n : ℤ) :
    Integrable (fun t : ℝ => Real.sin ((n:ℝ)*t)) (volume.restrict (Ioc 0 (2*Real.pi))) :=
  (show Continuous (fun t : ℝ => Real.sin ((n:ℝ)*t)) by fun_prop).integrableOn_Ioc

lemma periodic_cos_cos_integral (n m : ℤ) :
    (∫ t in Ioc 0 (2*Real.pi),Real.cos ((n:ℝ)*t)*Real.cos ((m:ℝ)*t))=
      ((if n-m=0 then 2*Real.pi else 0)+(if n+m=0 then 2*Real.pi else 0))/2 := by
  have he (t : ℝ) : Real.cos ((n:ℝ)*t)*Real.cos ((m:ℝ)*t)=
      (Real.cos (((n-m:ℤ):ℝ)*t)+Real.cos (((n+m:ℤ):ℝ)*t))/2 := by
    simp only [Int.cast_sub,Int.cast_add,sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [integral_div,integral_add (periodic_cos_integrable _) (periodic_cos_integrable _),
    periodic_cos_integral,periodic_cos_integral]

lemma periodic_sin_sin_integral (n m : ℤ) :
    (∫ t in Ioc 0 (2*Real.pi),Real.sin ((n:ℝ)*t)*Real.sin ((m:ℝ)*t))=
      ((if n-m=0 then 2*Real.pi else 0)-(if n+m=0 then 2*Real.pi else 0))/2 := by
  have he (t : ℝ) : Real.sin ((n:ℝ)*t)*Real.sin ((m:ℝ)*t)=
      (Real.cos (((n-m:ℤ):ℝ)*t)-Real.cos (((n+m:ℤ):ℝ)*t))/2 := by
    simp only [Int.cast_sub,Int.cast_add,sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [integral_div,integral_sub (periodic_cos_integrable _) (periodic_cos_integrable _),
    periodic_cos_integral,periodic_cos_integral]

lemma periodic_cos_sin_integral (n m : ℤ) :
    (∫ t in Ioc 0 (2*Real.pi),Real.cos ((n:ℝ)*t)*Real.sin ((m:ℝ)*t))=0 := by
  have he (t : ℝ) : Real.cos ((n:ℝ)*t)*Real.sin ((m:ℝ)*t)=
      (Real.sin (((m+n:ℤ):ℝ)*t)+Real.sin (((m-n:ℤ):ℝ)*t))/2 := by
    simp only [Int.cast_sub,Int.cast_add,sub_mul,add_mul,Real.sin_sub,Real.sin_add]
    ring
  simp_rw [he]
  rw [integral_div,integral_add (periodic_sin_integrable _) (periodic_sin_integrable _),
    periodic_sin_integral,periodic_sin_integral]
  norm_num

#print axioms periodic_cos_cos_integral
#print axioms periodic_sin_sin_integral
#print axioms periodic_cos_sin_integral
end BecknerOnofri.Friedrichs

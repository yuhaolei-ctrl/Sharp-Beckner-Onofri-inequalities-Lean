import BecknerOnofri.SmoothTorusFourierDerivative
import Legacy.TorusEndpoint.GreenMultiplierSummability
import Legacy.BecknerOnofri.RadialWiener
import Mathlib.Analysis.Real.Pi.Bounds

/-! Every polynomially weighted Fourier coefficient of a raw smooth torus
function is uniformly bounded. All bounds come from its actual derivatives. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.SmoothTorus
open HighDim

theorem coefficient_norm_le {d : ℕ} (f : C(Torus d,ℂ)) (k : Frequency d) :
    ‖coefficient f k‖ ≤ ‖f‖ := by
  have hc : Continuous (fun x => UnitAddTorus.mFourier (-k) x * f x) :=
    (UnitAddTorus.mFourier (-k)).continuous.mul f.continuous
  calc
    _ ≤ ∫ x,‖UnitAddTorus.mFourier (-k) x * f x‖ ∂torusMeasure d :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Torus d,‖f‖ ∂torusMeasure d := integral_mono
      (hc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _) (fun x => by
        rw [norm_mul,mFourier_norm_apply,one_mul]
        exact f.norm_coe_le_norm x)
    _ = _ := by simp

theorem coordinate_power_bound {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f)
    (j : Fin d) (m : ℕ) (k : Frequency d) :
    |(k j : ℝ)|^m * ‖coefficient f k‖ ≤
      ‖(⟨iterPartial j f m,smooth_continuous (iterPartial_smooth hf j m)⟩ : C(Torus d,ℂ))‖ := by
  have h := coefficient_norm_le
    (⟨iterPartial j f m,smooth_continuous (iterPartial_smooth hf j m)⟩ : C(Torus d,ℂ)) k
  change ‖coefficient (iterPartial j f m) k‖ ≤ _ at h
  rw [coefficient_iterPartial hf,norm_mul,norm_pow] at h
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_I,Complex.norm_intCast,mul_one] at h
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (abs_nonneg _) _ m
  have hpi := Real.pi_gt_three
  nlinarith [abs_nonneg (k j : ℝ)]

theorem largest_coordinate {d : ℕ} {k : Frequency d} (hk : k ≠ 0) :
    ∃ j : Fin d, 1 ≤ |(k j : ℝ)| ∧
      1 + frequencyLength k ≤ ((d:ℝ)+1)*|(k j : ℝ)| := by
  classical
  have hn : ∃ i : Fin d,k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  obtain ⟨i,hi⟩ := hn
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j => |(k j : ℝ)|)
    ⟨i,Finset.mem_univ i⟩
  have hj1 : 1 ≤ |(k j : ℝ)| :=
    le_trans (by exact_mod_cast Int.one_le_abs hi) (hj i (Finset.mem_univ i))
  have hd : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by have := i.isLt; omega)
  have hs : ∑ l : Fin d,(k l : ℝ)^2 ≤ (d:ℝ)*|(k j:ℝ)|^2 := by
    calc
      _ = ∑ l : Fin d,|(k l:ℝ)|^2 := by simp
      _ ≤ ∑ _ : Fin d,|(k j:ℝ)|^2 := Finset.sum_le_sum (fun l _ =>
        pow_le_pow_left₀ (abs_nonneg _) (hj l (Finset.mem_univ l)) 2)
      _ = _ := by simp
  have hr : frequencyLength k ≤ (d:ℝ)*|(k j:ℝ)| := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    calc
      _ ≤ (d:ℝ)*|(k j:ℝ)|^2 := hs
      _ ≤ (d:ℝ)^2*|(k j:ℝ)|^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ = _ := by ring
  exact ⟨j,hj1,by nlinarith⟩

theorem rapid_coefficient_bound {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f) (m : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ k : Frequency d,
      (1+frequencyLength k)^m * ‖coefficient f k‖ ≤ C := by
  let F : C(Torus d,ℂ) := ⟨f,smooth_continuous hf⟩
  let D (j : Fin d) : C(Torus d,ℂ) :=
    ⟨iterPartial j f m,smooth_continuous (iterPartial_smooth hf j m)⟩
  let B : ℝ := ∑ j : Fin d,‖D j‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  refine ⟨((d:ℝ)+1)^m*B+‖F‖,by positivity,?_⟩
  intro k
  by_cases hk : k=0
  · subst k
    have h := coefficient_norm_le F 0
    change ‖coefficient f 0‖ ≤ ‖F‖ at h
    simp only [frequencyLength,Pi.zero_apply,Int.cast_zero,zero_pow (by omega : 2 ≠ 0),
      Finset.sum_const_zero,Real.sqrt_zero,add_zero,one_pow,one_mul]
    exact h.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) hB))
  · obtain ⟨j,_,hj⟩ := largest_coordinate hk
    have hc : |(k j:ℝ)|^m*‖coefficient f k‖ ≤ B :=
      (coordinate_power_bound hf j m k).trans
        (Finset.single_le_sum (fun l _ => norm_nonneg (D l)) (Finset.mem_univ j))
    calc
      _ ≤ (((d:ℝ)+1)*|(k j:ℝ)|)^m*‖coefficient f k‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg zero_le_one (Real.sqrt_nonneg _)) hj m) (norm_nonneg _)
      _ = ((d:ℝ)+1)^m*(|(k j:ℝ)|^m*‖coefficient f k‖) := by rw [mul_pow]; ring
      _ ≤ ((d:ℝ)+1)^m*B := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)

theorem rapid_summable {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f) (m : ℕ) :
    Summable (fun k : Frequency d => (1+frequencyLength k)^m * ‖coefficient f k‖) := by
  obtain ⟨C,hC,hbound⟩ := rapid_coefficient_bound hf (m+2*d)
  apply ((Legacy.TorusEndpoint.GreenMultiplierSummability.summable_productMajorant d).mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _) (norm_nonneg _))
  intro k
  have hr : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  have hp : 0 < 1+frequencyLength k := by positivity
  have hs : (frequencyLength k)^2 =
      Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (k i : ℝ)))
  have hb : (1+frequencyLength k)^m * ‖coefficient f k‖ ≤
      C / (1+frequencyLength k)^(2*d) := by
    apply (le_div_iff₀ (pow_pos hp _)).mpr
    have h := hbound k
    rw [pow_add] at h
    nlinarith [h]
  calc
    _ ≤ C / (1+frequencyLength k)^(2*d) := hb
    _ ≤ C / (1+(frequencyLength k)^2)^d := by
      apply div_le_div_of_nonneg_left hC (by positivity)
      rw [pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    _ = C*((1+Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k)⁻¹^d) := by
      rw [hs,div_eq_mul_inv,inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Legacy.TorusEndpoint.GreenMultiplierSummability.shifted_radial_inv_le_product k) hC

/-- Raw smoothness alone implies every absolutely summable Fourier moment. -/
theorem smooth_fourier_moments {d : ℕ} {f : Torus d → ℝ} (hf : SmoothOnTorus f)
    (m : ℕ) :
    Summable (fun k : Frequency d => (1+frequencyLength k)^m * ‖fourierCoeff f k‖) :=
  rapid_summable (of_real hf) m

#print axioms rapid_coefficient_bound
#print axioms smooth_fourier_moments
end BecknerOnofri.SmoothTorus

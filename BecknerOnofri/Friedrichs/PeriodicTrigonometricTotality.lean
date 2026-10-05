module

public import BecknerOnofri.Friedrichs.PeriodicFourierTotality

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.Friedrichs

lemma periodic_fourier_value (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle (2*Real.pi))=
      (Real.cos ((n:ℝ)*t):ℂ)+(Real.sin ((n:ℝ)*t):ℂ)*Complex.I := by
  rw [fourier_coe_apply]
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ)/(2*Real.pi))=
      (((n:ℝ)*t:ℝ):ℂ)*Complex.I := by
    push_cast
    field_simp
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [he,Complex.exp_ofReal_mul_I]

abbrev PeriodicRealL2 := Lp ℝ 2 (volume.restrict (Ioc 0 (2*Real.pi)))

lemma periodic_trigonometric_total (f : PeriodicRealL2)
    (hc : ∀ n : ℤ,(∫ t in Ioc 0 (2*Real.pi),Real.cos ((n:ℝ)*t)*f t)=0)
    (hs : ∀ n : ℤ,(∫ t in Ioc 0 (2*Real.pi),Real.sin ((n:ℝ)*t)*f t)=0) : f=0 := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))
  have hF : MemLp (fun t => (f t:ℂ)) 2 μ := (Lp.memLp f).ofReal
  let F : PeriodicComplexL2 := hF.toLp (fun t => (f t:ℂ))
  have hz : F=0 := periodic_coefficients_total F (fun n => by
    rw [fourierCoeffOn_congr_ae (by positivity : (0:ℝ)<2*Real.pi) hF.coeFn_toLp]
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero,intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
    have hcm : MemLp (fun t : ℝ => Real.cos ((n:ℝ)*t)) 2 μ :=
      MemLp.of_bound (by fun_prop) 1 (ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((n:ℝ)*t)))
    have hsm : MemLp (fun t : ℝ => Real.sin ((n:ℝ)*t)) 2 μ :=
      MemLp.of_bound (by fun_prop) 1 (ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ((n:ℝ)*t)))
    have hci : Integrable (fun t => Real.cos ((n:ℝ)*t)*f t) μ := hcm.integrable_mul (Lp.memLp f)
    have hsi : Integrable (fun t => Real.sin ((n:ℝ)*t)*f t) μ := hsm.integrable_mul (Lp.memLp f)
    have he (t : ℝ) : fourier (-n) (t : AddCircle (2*Real.pi)) • (f t:ℂ)=
        ((Real.cos ((n:ℝ)*t)*f t:ℝ):ℂ)-Complex.I*((Real.sin ((n:ℝ)*t)*f t:ℝ):ℂ) := by
      rw [periodic_fourier_value]
      simp only [Int.cast_neg,neg_mul,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,
        Complex.ofReal_mul,smul_eq_mul]
      ring
    have hperiod (t : ℝ) : fourier (-n) (t : AddCircle (2*Real.pi-0))=
        fourier (-n) (t : AddCircle (2*Real.pi)) := by
      simp only [fourier_coe_apply,sub_zero]
    simp_rw [hperiod]
    change (1/(2*Real.pi):ℝ) • (∫ t,fourier (-n) (t : AddCircle (2*Real.pi)) • (f t:ℂ) ∂μ)=0
    simp_rw [he]
    have hcc : Integrable (fun t => ((Real.cos ((n:ℝ)*t)*f t:ℝ):ℂ)) μ := hci.ofReal
    have hss : Integrable (fun t => ((Real.sin ((n:ℝ)*t)*f t:ℝ):ℂ)) μ := hsi.ofReal
    have hzero : (∫ t,((Real.cos ((n:ℝ)*t)*f t:ℝ):ℂ)-Complex.I*((Real.sin ((n:ℝ)*t)*f t:ℝ):ℂ) ∂μ)=0 := by
      calc
        _ = (∫ t,((Real.cos ((n:ℝ)*t)*f t:ℝ):ℂ) ∂μ)-
            ∫ t,Complex.I*((Real.sin ((n:ℝ)*t)*f t:ℝ):ℂ) ∂μ := integral_sub hcc (hss.const_mul Complex.I)
        _ = 0 := by
          rw [integral_const_mul,integral_complex_ofReal,integral_complex_ofReal,hc n,hs n]
          simp
    rw [hzero,smul_zero])
  apply Lp.ext
  have ha : ∀ᵐ t ∂μ,(f t:ℂ)=0 := by
    filter_upwards [hF.coeFn_toLp,Lp.coeFn_zero ℂ 2 μ] with t ht h0
    change F t=(f t:ℂ) at ht
    rw [hz,h0] at ht
    exact ht.symm
  filter_upwards [ha,Lp.coeFn_zero ℝ 2 μ] with t ht h0
  exact (Complex.ofReal_eq_zero.mp ht).trans h0.symm

#print axioms periodic_trigonometric_total
end BecknerOnofri.Friedrichs

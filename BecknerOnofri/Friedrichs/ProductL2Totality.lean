import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini and Cauchy--Schwarz for tensor completeness in actual product L2 spaces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma integral_sq_toLp {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x,f x^2 ∂μ)=‖hf.toLp f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx,pow_two,real_inner_comm]

lemma integral_mul_eq_inner {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,f x*g x ∂μ)=inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp only [hx,hy,RCLike.inner_apply,conj_trivial]
  ring

lemma integral_mul_sq_le {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,f x*g x ∂μ)^2≤(∫ x,f x^2 ∂μ)*(∫ x,g x^2 ∂μ) := by
  rw [integral_mul_eq_inner hf hg,integral_sq_toLp hf,integral_sq_toLp hg]
  have h := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h
  simpa only [Real.norm_eq_abs,sq_abs,mul_pow] using hs

lemma memLp_product {f : X → ℝ} {g : Y → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : X×Y => f p.1*g p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq (hf.1.comp_fst.mul hg.1.comp_snd)).mpr
  simpa only [Pi.mul_apply,mul_pow] using hf.integrable_sq.mul_prod hg.integrable_sq

lemma memLp_fibers {F : X×Y → ℝ} (hF : MemLp F 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν,MemLp (fun x => F (x,y)) 2 μ := by
  filter_upwards [hF.1.prodMk_right,hF.integrable_sq.prod_left_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

lemma coefficient_memLp {F : X×Y → ℝ} {u : X → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) (hu : MemLp u 2 μ) :
    MemLp (fun y => ∫ x,u x*F (x,y) ∂μ) 2 ν := by
  have hm : AEStronglyMeasurable (fun y => ∫ x,u x*F (x,y) ∂μ) ν :=
    (hu.1.comp_fst.mul hF.1).prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hbound : Integrable (fun y => (∫ x,u x^2 ∂μ)*(∫ x,F (x,y)^2 ∂μ)) ν :=
    hF.integrable_sq.integral_prod_right.const_mul _
  apply hbound.mono' (hm.pow 2)
  filter_upwards [memLp_fibers hF] with y hy
  simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_sq] using integral_mul_sq_le hu hy

/-- Totality tensorizes for countable families in finite-measure real L2 spaces. -/
theorem tensor_total {I J : Type*} [Countable I]
    (u : I → X → ℝ) (v : J → Y → ℝ)
    (hu : ∀ i,MemLp (u i) 2 μ) (hv : ∀ j,MemLp (v j) 2 ν)
    (hTu : ∀ f : Lp ℝ 2 μ,(∀ i,(∫ x,u i x*f x ∂μ)=0) → f=0)
    (hTv : ∀ f : Lp ℝ 2 ν,(∀ j,(∫ y,v j y*f y ∂ν)=0) → f=0)
    {F : X×Y → ℝ} (hF : MemLp F 2 (μ.prod ν))
    (h : ∀ i j,(∫ p,u i p.1*v j p.2*F p ∂μ.prod ν)=0) : F=ᵐ[μ.prod ν] 0 := by
  have hc (i : I) : (fun y => ∫ x,u i x*F (x,y) ∂μ)=ᵐ[ν] 0 := by
    let q : Y → ℝ := fun y => ∫ x,u i x*F (x,y) ∂μ
    have hq : MemLp q 2 ν := coefficient_memLp hF (hu i)
    have hz : hq.toLp q=0 := by
      apply hTv
      intro j
      calc
        _ = ∫ y,v j y*q y ∂ν := by
          apply integral_congr_ae
          filter_upwards [hq.coeFn_toLp] with y hy
          rw [hy]
        _ = ∫ p,u i p.1*v j p.2*F p ∂μ.prod ν := by
          have hI : Integrable (fun p : X×Y => u i p.1*v j p.2*F p) (μ.prod ν) :=
            (memLp_product (hu i) (hv j)).integrable_mul hF
          rw [integral_prod_symm _ hI]
          apply integral_congr_ae
          apply ae_of_all
          intro y
          dsimp [q]
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact ae_of_all _ (fun x => by ring)
        _ = 0 := h i j
    exact hq.coeFn_toLp.symm.trans (hz ▸ Lp.coeFn_zero ℝ 2 ν)
  have hzero : ∀ᵐ y ∂ν,(fun x => F (x,y))=ᵐ[μ] 0 := by
    filter_upwards [memLp_fibers hF,ae_all_iff.mpr hc] with y hy hcy
    have hz : hy.toLp (fun x => F (x,y))=0 := by
      apply hTu
      intro i
      calc
        _ = ∫ x,u i x*F (x,y) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hy.coeFn_toLp] with x hx
          rw [hx]
        _ = 0 := hcy i
    exact hy.coeFn_toLp.symm.trans (hz ▸ Lp.coeFn_zero ℝ 2 μ)
  have hi : (∫ p,F p^2 ∂μ.prod ν)=0 := by
    rw [integral_prod_symm _ hF.integrable_sq]
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with y hy
    calc
      _ = ∫ x,(0:ℝ) ∂μ := integral_congr_ae (hy.mono (fun x hx => by simp [hx]))
      _ = 0 := integral_zero _ _
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p => sq_nonneg (F p))) hF.integrable_sq).mp hi
  filter_upwards [hz] with p hp
  exact (sq_eq_zero_iff).mp hp

#print axioms tensor_total
end BecknerOnofri.Friedrichs.ProductL2

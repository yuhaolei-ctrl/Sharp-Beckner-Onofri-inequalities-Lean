module

public import BecknerOnofri.SpatialThetaJacobiSpectrum

@[expose] public section

/-! The normalized Jacobi product identity for the actual spatial theta
function, derived from the genuine Banach product and its Fourier spectrum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SpatialThetaJacobi
open SpatialThetaProduct

theorem fourier_one_re (y : ℝ) :
    (fourier 1 (y:UnitAddCircle)).re=Real.cos (2*Real.pi*y) := by
  rw [fourier_coe_apply]
  have he : (2*Real.pi*Complex.I*(1:ℤ)*(y:ℂ)/(1:ℝ))=
      ((2*Real.pi*y:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I_re]

theorem paired_factor (t y : ℝ) (n : ℕ) :
    (1+(qMode t n:ℂ)*fourier 1 (y:UnitAddCircle))*
      (1+(qMode t n:ℂ)*fourier (-1) (y:UnitAddCircle))=
      (((1+qMode t n)^2*factor t (Real.sin (Real.pi*y)^2) n:ℝ):ℂ) := by
  have hs : fourier 1 (y:UnitAddCircle)+fourier (-1) (y:UnitAddCircle)=
      (2*Real.cos (2*Real.pi*y):ℝ) := by
    rw [fourier_neg]
    apply Complex.ext
    · simp only [Complex.add_re,Complex.conj_re,Complex.ofReal_re,fourier_one_re]
      ring
    · simp only [Complex.add_im,Complex.conj_im,Complex.ofReal_im,add_neg_cancel]
  have hm : fourier 1 (y:UnitAddCircle)*fourier (-1) (y:UnitAddCircle)=(1:ℂ) := by
    rw [← fourier_add]
    norm_num
  have hden : (1+qMode t n)^2≠0 := pow_ne_zero _ (by linarith [qMode_pos t n])
  have hc : Real.cos (2*Real.pi*y)=1-2*Real.sin (Real.pi*y)^2 := by
    rw [show 2*Real.pi*y=2*(Real.pi*y) by ring,Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*y)]
  calc
    _ = 1+(qMode t n:ℂ)*(fourier 1 (y:UnitAddCircle)+fourier (-1) (y:UnitAddCircle))+
        (qMode t n:ℂ)^2*(fourier 1 (y:UnitAddCircle)*fourier (-1) (y:UnitAddCircle)) := by ring
    _ = ((1+qMode t n*(2*Real.cos (2*Real.pi*y))+(qMode t n)^2:ℝ):ℂ) := by
      rw [hs,hm]; push_cast; ring
    _ = _ := by
      congr 1
      rw [hc]
      unfold factor SpatialThetaProduct.coefficient
      conv_rhs => rw [mul_sub,mul_one,← mul_assoc,mul_div_cancel₀ _ hden]
      ring

theorem evaluate_finite_normalized (t y : ℝ) (N : ℕ) :
    evaluate 1 one_ne_zero (finiteLaurent t N) (y:UnitAddCircle)=
      evaluate 1 one_ne_zero (finiteLaurent t N) 0*
      ((∏ n∈Finset.range N,factor t (Real.sin (Real.pi*y)^2) n:ℝ):ℂ) := by
  simp only [evaluate_finiteLaurent,inv_one,mul_one,ContinuousMap.mul_apply,
    ContinuousMap.prod_apply,ContinuousMap.add_apply,ContinuousMap.one_apply,
    ContinuousMap.smul_apply,smul_eq_mul,fourier_eval_zero]
  rw [← Finset.prod_mul_distrib]
  simp_rw [paired_factor]
  rw [← Complex.ofReal_prod,Finset.prod_mul_distrib,Complex.ofReal_mul]
  congr 1
  simp only [← Complex.ofReal_add,← Complex.ofReal_one,← Complex.ofReal_prod]
  rw [← Complex.ofReal_mul,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro n _
  ring

theorem evaluate_finite_zero_re_ge_one (t : ℝ) (N : ℕ) :
    1≤(evaluate 1 one_ne_zero (finiteLaurent t N) 0).re := by
  simp only [evaluate_finiteLaurent,inv_one,mul_one,ContinuousMap.mul_apply,
    ContinuousMap.prod_apply,ContinuousMap.add_apply,ContinuousMap.one_apply,
    ContinuousMap.smul_apply,smul_eq_mul,fourier_eval_zero]
  simp only [← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_prod,
    ← Complex.ofReal_mul,Complex.ofReal_re]
  have hp : 1≤∏ n∈Finset.range N,(1+qMode t n) :=
    Finset.one_le_prod (fun n _ => by linarith [qMode_pos t n])
  nlinarith

theorem pairedProduct_zero_ne_zero {t : ℝ} (ht : 0<t) :
    pairedProduct t 1 (0:UnitAddCircle)≠0 := by
  have hlim := ((Complex.continuous_re.comp (ContinuousMap.evalCLM ℂ (0:UnitAddCircle)).continuous).continuousAt.tendsto).comp (tendsto_evaluate ht 1 one_ne_zero)
  have hbound : 1≤(pairedProduct t 1 (0:UnitAddCircle)).re :=
    ge_of_tendsto' hlim (evaluate_finite_zero_re_ge_one t)
  intro he
  rw [he] at hbound
  norm_num at hbound

theorem pairedProduct_normalized {t : ℝ} (ht : 0<t) (y : ℝ) :
    pairedProduct t 1 (y:UnitAddCircle)=pairedProduct t 1 (0:UnitAddCircle)*
      (jacobiProduct t (Real.sin (Real.pi*y)^2):ℂ) := by
  have hr : Real.sin (Real.pi*y)^2∈Icc (0:ℝ) 1 := by
    refine ⟨sq_nonneg _,?_⟩
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*y),sq_nonneg (Real.cos (Real.pi*y))]
  have hj := (Real.hasProd_of_hasSum_log (factor_pos ht hr) (log_summable ht _).hasSum).multipliable.tendsto_prod_tprod_nat
  have hx := (ContinuousMap.evalCLM ℂ (y:UnitAddCircle)).continuous.continuousAt.tendsto.comp
    (tendsto_evaluate ht 1 one_ne_zero)
  have hz := (ContinuousMap.evalCLM ℂ (0:UnitAddCircle)).continuous.continuousAt.tendsto.comp
    (tendsto_evaluate ht 1 one_ne_zero)
  have hright := hz.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hj)
  exact tendsto_nhds_unique hx (hright.congr' (Eventually.of_forall
    (fun N => (evaluate_finite_normalized t y N).symm)))

theorem thetaMap_real {t : ℝ} (ht : 0<t) (y : ℝ) :
    thetaMap t (y:UnitAddCircle)=(RadialThetaTail.theta t y:ℂ) := by
  rw [thetaMap_apply ht]
  exact Legacy.TorusEndpoint.TorusHeatPositivity.theta_eq_ofReal_re
    (div_pos ht Real.pi_pos) _

/-- Actual normalized Jacobi identity; the common product normalization is
cancelled only after proving it nonzero from convergent positive approximants. -/
theorem theta_eq_zero_mul_product {t : ℝ} (ht : 0<t) (y : ℝ) :
    RadialThetaTail.theta t y=RadialThetaTail.theta t 0*
      jacobiProduct t (Real.sin (Real.pi*y)^2) := by
  have hC : coefficient 0 (pairedProduct t 1)≠0 := by
    intro he
    have hh := pairedProduct_zero_ne_zero ht
    apply hh
    rw [pairedProduct_eq_theta ht,he]
    simp only [ContinuousMap.smul_apply,smul_eq_mul,zero_mul]
  have hp := pairedProduct_normalized ht y
  rw [pairedProduct_eq_theta ht] at hp
  simp only [ContinuousMap.smul_apply,smul_eq_mul] at hp
  have hz : thetaMap t (0:UnitAddCircle)=(RadialThetaTail.theta t 0:ℂ) := by
    simpa only [AddCircle.coe_zero] using thetaMap_real ht 0
  rw [thetaMap_real ht y,hz,mul_assoc] at hp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul]
  exact mul_left_cancel₀ hC hp

#print axioms theta_eq_zero_mul_product
end BecknerOnofri.HighDim.SpatialThetaJacobi

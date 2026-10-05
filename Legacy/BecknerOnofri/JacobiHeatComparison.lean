module

public import Legacy.BecknerOnofri.JacobiHeatNonnegative
public import Legacy.BecknerOnofri.JacobiHeatFiniteComparison

@[expose] public section

/-! Actual Jacobi heat-kernel domination by the Dirichlet m=1 kernel.
The initial data are matched using genuine polynomial approximation from above. -/
noncomputable section
open Set MeasureTheory Filter Polynomial Classical
open scoped ContDiff Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiEigenfunctions JacobiHeatBounds

/-- The actual kernel actions are compared on every nonnegative angular polynomial. -/
theorem polynomialHeat_le_dirichlet_action {m : ℕ} (hm : 0<m) (p : Polynomial ℝ)
    (hp : ∀z∈Icc (-1:ℝ) 1,0≤p.eval z) {t x : ℝ} (ht : 0<t)
    (hx : x∈Icc 0 Real.pi) :
    polynomialHeat m p t x ≤ Real.exp (-potentialBottom m*t)*
      (∫y,heatKernel 1 t x y*angularPolynomial m p y ∂intervalMeasure) := by
  let g : ℝ→ℝ := fun y => Real.sin y^(m-1)*p.eval (Real.cos y)
  have hgc : Continuous g := (Real.continuous_sin.pow (m-1)).mul
    ((JacobiAngular.polynomial_contDiff p).continuous.comp Real.continuous_cos)
  have hg : ∀y,angularPolynomial m p y=Real.sin y*g y := by
    intro y
    dsimp [angularPolynomial,g]
    rw [← mul_assoc,← pow_succ',Nat.sub_add_cancel hm]
  let w : ℝ→ℝ := fun y => heatKernel 1 t x y*Real.sin y
  have hwc : Continuous w := (heatKernel_continuous_right 1 ht x).mul Real.continuous_sin
  have hw : Integrable w intervalMeasure := hwc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  let M : ℝ := ∫y,‖w y‖ ∂intervalMeasure
  let E : ℝ := Real.exp (-potentialBottom m*t)
  have hM : 0≤M := integral_nonneg (fun _ => norm_nonneg _)
  have hE : 0<E := Real.exp_pos _
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε/(2*(E*M+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨q,hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun z => g (Real.arccos z)) (hgc.comp Real.continuous_arccos).continuousOn δ hδ
  let Q : Polynomial ℝ := q+C δ
  have herr (y : ℝ) (hy : y∈Icc 0 Real.pi) :
      0≤Q.eval (Real.cos y)-g y ∧ ‖Q.eval (Real.cos y)-g y‖≤2*δ := by
    have he := hq (Real.cos y) ⟨Real.neg_one_le_cos y,Real.cos_le_one y⟩
    rw [Real.arccos_cos hy.1 hy.2] at he
    have he' := abs_lt.mp he
    simp only [Q,eval_add,eval_C,Real.norm_eq_abs]
    constructor
    · linarith [he'.1]
    · rw [abs_le]
      constructor <;> linarith [he'.1,he'.2]
  have horder (y : ℝ) (hy : y∈Icc 0 Real.pi) :
      polynomialHeat m p 0 y ≤ polynomialHeat 1 Q 0 y := by
    rw [polynomialHeat_initial,polynomialHeat_initial,hg]
    change Real.sin y*g y≤Real.sin y^1*Q.eval (Real.cos y)
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp (herr y hy).1)
      (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2)
  have hnonneg (y : ℝ) (hy : y∈Icc 0 Real.pi) : 0≤polynomialHeat m p 0 y :=
    polynomialHeat_nonnegative hm p hp (le_refl 0) hy
  have hfinite := finiteHeat_le_decayed_dirichlet hm
    ((polynomialBasis m).repr p).support ((polynomialBasis 1).repr Q).support
    (polynomialCoefficients m p) (polynomialCoefficients 1 Q) hnonneg horder ht.le hx
  change polynomialHeat m p t x≤E*polynomialHeat 1 Q t x at hfinite
  rw [← heatKernel_polynomial 1 (by decide) Q ht x] at hfinite
  have hQc : Continuous (fun y => Q.eval (Real.cos y)) :=
    (JacobiAngular.polynomial_contDiff Q).continuous.comp Real.continuous_cos
  have hwi : Integrable (fun y => w y*Q.eval (Real.cos y)) intervalMeasure :=
    (hwc.mul hQc).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hwgi : Integrable (fun y => w y*g y) intervalMeasure :=
    (hwc.mul hgc).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hdiff : Integrable (fun y => w y*(Q.eval (Real.cos y)-g y)) intervalMeasure :=
    (hwc.mul (hQc.sub hgc)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hbound : (∫y,‖w y*(Q.eval (Real.cos y)-g y)‖ ∂intervalMeasure) ≤ 2*δ*M := by
    rw [show 2*δ*M = ∫y,(2*δ)*‖w y‖ ∂intervalMeasure by rw [integral_const_mul]]
    apply integral_mono_ae hdiff.norm (hw.norm.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [norm_mul,mul_comm (2*δ)]
    exact mul_le_mul_of_nonneg_left (herr y ⟨hy.1.le,hy.2.le⟩).2 (norm_nonneg _)
  have hnorm := (norm_integral_le_integral_norm (μ:=intervalMeasure)
    (fun y => w y*(Q.eval (Real.cos y)-g y))).trans hbound
  have he : (∫y,w y*(Q.eval (Real.cos y)-g y) ∂intervalMeasure) =
      (∫y,w y*Q.eval (Real.cos y) ∂intervalMeasure)-(∫y,w y*g y ∂intervalMeasure) := by
    simp_rw [mul_sub]
    exact integral_sub hwi hwgi
  rw [he,Real.norm_eq_abs] at hnorm
  have hsmall : E*(2*δ*M)≤ε := by
    dsimp [δ]
    rw [show E*(2*(ε/(2*(E*M+1)))*M)=ε*(E*M)/(E*M+1) by field_simp]
    apply (div_le_iff₀ (by positivity : 0<E*M+1)).mpr
    nlinarith
  have hd := mul_le_mul_of_nonneg_left (abs_le.mp hnorm).2 hE.le
  have hr : E*(∫y,w y*Q.eval (Real.cos y) ∂intervalMeasure) ≤
      E*(∫y,w y*g y ∂intervalMeasure)+ε := by nlinarith
  simp only [angularPolynomial,pow_one,← mul_assoc] at hfinite
  change polynomialHeat m p t x≤E*(∫y,w y*Q.eval (Real.cos y) ∂intervalMeasure) at hfinite
  have hi : (∫y,heatKernel 1 t x y*angularPolynomial m p y ∂intervalMeasure) =
      ∫y,w y*g y ∂intervalMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hg]
    exact (mul_assoc _ _ _).symm
  rw [hi]
  exact hfinite.trans hr

/-- Quantitative actual kernel comparison. No assumed positivity or heat-kernel order is used. -/
theorem heatKernel_le_decayed_dirichlet {m : ℕ} (hm : 0<m) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Icc 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    heatKernel m t x y≤Real.exp (-potentialBottom m*t)*heatKernel 1 t x y := by
  apply sub_nonneg.mp
  apply nonnegative_of_angularPolynomial_tests m
    ((continuous_const.mul (heatKernel_continuous_right 1 ht x)).sub
      (heatKernel_continuous_right m ht x)) _ hy
  intro p hp
  have hg : Integrable (angularPolynomial m p) intervalMeasure :=
    (angularPolynomial_memLp m p).integrable (by norm_num)
  have hi1 := (heatKernel_mul_integrable 1 ht x hg).const_mul (Real.exp (-potentialBottom m*t))
  have him := heatKernel_mul_integrable m ht x hg
  change 0≤∫y,(Real.exp (-potentialBottom m*t)*heatKernel 1 t x y-heatKernel m t x y)*angularPolynomial m p y ∂intervalMeasure
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub hi1 him,integral_const_mul,heatKernel_polynomial m hm p ht x]
  exact sub_nonneg.mpr (polynomialHeat_le_dirichlet_action hm p hp ht hx)

#print axioms polynomialHeat_le_dirichlet_action
#print axioms heatKernel_le_decayed_dirichlet
end Legacy.BecknerOnofri.JacobiHeatPositivity

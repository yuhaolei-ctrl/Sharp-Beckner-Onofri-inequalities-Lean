module

public import Legacy.BecknerOnofri.JacobiCompleteness

@[expose] public section

/-! Nonnegative angular polynomial tests detect pointwise positivity of a continuous kernel.
The extension to arbitrary nonnegative continuous tests is proved by positive polynomial
approximation on the closed cosine interval. -/
noncomputable section
open Set MeasureTheory Filter Polynomial Classical
open scoped Topology ContDiff
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiEigenfunctions

theorem continuous_interval_integrable {f : ℝ→ℝ} (hf : Continuous f) :
    Integrable f intervalMeasure :=
  hf.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- Actual polynomial test positivity extends to all actual continuous nonnegative tests. -/
theorem continuous_test_nonnegative (m : ℕ) {K : ℝ→ℝ} (hK : Continuous K)
    (hpoly : ∀p : Polynomial ℝ, (∀z∈Icc (-1:ℝ) 1,0≤p.eval z) →
      0≤∫y,K y*angularPolynomial m p y ∂intervalMeasure)
    {g : ℝ→ℝ} (hg : Continuous g) (hgn : ∀y∈Icc 0 Real.pi,0≤g y) :
    0≤∫y,(K y*Real.sin y^m)*g y ∂intervalMeasure := by
  let w : ℝ→ℝ := fun y => K y*Real.sin y^m
  have hwc : Continuous w := hK.mul (Real.continuous_sin.pow m)
  have hw : Integrable w intervalMeasure := continuous_interval_integrable hwc
  have hwg : Integrable (fun y => w y*g y) intervalMeasure := continuous_interval_integrable (hwc.mul hg)
  let M : ℝ := ∫y,‖w y‖ ∂intervalMeasure
  have hM : 0≤M := integral_nonneg (fun _ => norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε/(2*(M+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun z => g (Real.arccos z)) (hg.comp Real.continuous_arccos).continuousOn δ hδ
  let q : Polynomial ℝ := p+C δ
  have hq : ∀z∈Icc (-1:ℝ) 1,0≤q.eval z := by
    intro z hz
    have he := (abs_lt.mp (hp z hz)).1
    have hg' := hgn (Real.arccos z) ⟨Real.arccos_nonneg z,Real.arccos_le_pi z⟩
    simp only [q,eval_add,eval_C]
    linarith
  have herr : ∀y∈Ioo 0 Real.pi, ‖q.eval (Real.cos y)-g y‖≤2*δ := by
    intro y hy
    have he := (hp (Real.cos y) ⟨Real.neg_one_le_cos y,Real.cos_le_one y⟩).le
    rw [Real.arccos_cos hy.1.le hy.2.le] at he
    change |p.eval (Real.cos y)-g y|≤δ at he
    simp only [q,eval_add,eval_C,Real.norm_eq_abs]
    calc
      _=|(p.eval (Real.cos y)-g y)+δ| := by congr 1; ring
      _≤|p.eval (Real.cos y)-g y|+|δ| := abs_add_le _ _
      _≤2*δ := by rw [abs_of_pos hδ]; linarith
  have hqc : Continuous (fun y => q.eval (Real.cos y)) :=
    (JacobiAngular.polynomial_contDiff q).continuous.comp Real.continuous_cos
  have hwq : Integrable (fun y => w y*q.eval (Real.cos y)) intervalMeasure :=
    continuous_interval_integrable (hwc.mul hqc)
  have hdiff : Integrable (fun y => w y*(q.eval (Real.cos y)-g y)) intervalMeasure :=
    continuous_interval_integrable (hwc.mul (hqc.sub hg))
  have hb : (∫y,‖w y*(q.eval (Real.cos y)-g y)‖ ∂intervalMeasure) ≤ 2*δ*M := by
    rw [show 2*δ*M = ∫y, (2*δ)*‖w y‖ ∂intervalMeasure by rw [integral_const_mul]]
    apply integral_mono_ae hdiff.norm (hw.norm.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [norm_mul,mul_comm (2*δ)]
    exact mul_le_mul_of_nonneg_left (herr y hy) (norm_nonneg _)
  have hsmall : 2*δ*M≤ε := by
    dsimp [δ]
    have hd : 0<M+1 := by positivity
    rw [show 2*(ε/(2*(M+1)))*M = ε*M/(M+1) by field_simp]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hnorm := (norm_integral_le_integral_norm
    (μ:=intervalMeasure) (fun y => w y*(q.eval (Real.cos y)-g y))).trans (hb.trans hsmall)
  have he : (∫y,w y*(q.eval (Real.cos y)-g y) ∂intervalMeasure) =
      (∫y,w y*q.eval (Real.cos y) ∂intervalMeasure) - (∫y,w y*g y ∂intervalMeasure) := by
    simp_rw [mul_sub]
    exact integral_sub hwq hwg
  rw [he,Real.norm_eq_abs] at hnorm
  have hp' := hpoly q hq
  change 0≤∫y,K y*(Real.sin y^m*q.eval (Real.cos y)) ∂intervalMeasure at hp'
  simp only [← mul_assoc] at hp'
  have hd := (abs_le.mp hnorm).2
  change 0≤(∫y,w y*g y ∂intervalMeasure)+ε
  linarith

/-- The weight is strictly positive in the open interval, so positive polynomial tests
force pointwise nonnegativity there. No spectral positivity is assumed. -/
theorem nonnegative_of_angularPolynomial_tests (m : ℕ) {K : ℝ→ℝ} (hK : Continuous K)
    (hpoly : ∀p : Polynomial ℝ, (∀z∈Icc (-1:ℝ) 1,0≤p.eval z) →
      0≤∫y,K y*angularPolynomial m p y ∂intervalMeasure)
    {x : ℝ} (hx : x∈Ioo 0 Real.pi) : 0≤K x := by
  by_contra! hn
  let g : ℝ→ℝ := fun y => max (-K y) 0
  have hgc : Continuous g := hK.neg.max continuous_const
  have htest := continuous_test_nonnegative m hK hpoly hgc (fun _ _ => le_max_right _ _)
  let F : ℝ→ℝ := fun y => -((K y*Real.sin y^m)*g y)
  have hFc : Continuous F := ((hK.mul (Real.continuous_sin.pow m)).mul hgc).neg
  have hFn : ∀y∈Icc 0 Real.pi,0≤F y := by
    intro y hy
    have hs : 0≤Real.sin y^m := pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2) _
    change 0≤-((K y*Real.sin y^m)*max (-K y) 0)
    by_cases hk : K y≤0
    · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hk hs) (le_max_right _ _))
    · rw [max_eq_right (by linarith : -K y≤0),mul_zero,neg_zero]
  have hFx : 0<F x := by
    change 0< -((K x*Real.sin x^m)*max (-K x) 0)
    rw [max_eq_left (by linarith : 0≤-K x)]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hn (pow_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2) _)) (by linarith))
  have hp := intervalIntegral.integral_pos Real.pi_pos hFc.continuousOn (fun y hy => hFn y ⟨hy.1.le,hy.2⟩)
    ⟨x,⟨hx.1.le,hx.2.le⟩,hFx⟩
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] at hp
  change 0<∫y,-((K y*Real.sin y^m)*g y) ∂intervalMeasure at hp
  rw [integral_neg] at hp
  linarith

#print axioms nonnegative_of_angularPolynomial_tests
end Legacy.BecknerOnofri.JacobiHeatPositivity

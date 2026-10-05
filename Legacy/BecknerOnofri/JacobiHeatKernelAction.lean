module

public import Legacy.BecknerOnofri.JacobiHeatFinite
public import Legacy.BecknerOnofri.JacobiHeatSmooth
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Actual Jacobi heat-kernel action on finite spectral and angular-polynomial initial data. -/
noncomputable section
open Set MeasureTheory Filter Polynomial Classical
open scoped ContDiff Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiEigenfunctions JacobiHeatBounds

def kernelTerm (m n : ℕ) (t x y : ℝ) : ℝ :=
  Real.exp (-t*eigenvalue m n)*normalizedFunction m n x*normalizedFunction m n y

theorem kernelTerm_eq_heatTerm (m n : ℕ) (t x y : ℝ) :
    kernelTerm m n t x y = heatTerm m n ![t,x,y] := by
  rw [kernelTerm,heatTerm,Fin.prod_univ_three]
  simp only [heatFactor,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    ite_true,if_neg (show (1:Fin 3) ≠ 0 by decide),if_neg (show (2:Fin 3) ≠ 0 by decide)]
  rw [show -(eigenvalue m n)*t = -t*eigenvalue m n by ring]
  rfl

theorem kernelTerm_bound (m n : ℕ) {t : ℝ} (ht : 0<t) (x y : ℝ) :
    ‖kernelTerm m n t x y‖ ≤ heatMajorant m 0 t n := by
  rw [kernelTerm_eq_heatTerm]
  simpa only [norm_iteratedFDeriv_zero] using
    (heatTerm_derivative_bound m n 0 (z:=![t,x,y]) (ε:=t) (by simp [timeSlab]))

theorem heatKernel_continuous_right (m : ℕ) {t : ℝ} (ht : 0<t) (x : ℝ) :
    Continuous (heatKernel m t x) := by
  have hc : Continuous (fun y : ℝ => jointHeat m ![t,x,y]) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hcmap : Continuous (fun r : ℝ => (![t,x,r] : HeatSpace)) := by fun_prop
    exact (jointHeat_contDiffAt m (z:=![t,x,y]) (by simpa using ht)).continuousAt.comp
      (f:=fun r : ℝ => (![t,x,r] : HeatSpace)) hcmap.continuousAt
  simpa [jointHeat_eq_heatKernel] using hc

theorem heatKernel_summable (m : ℕ) {t : ℝ} (ht : 0<t) (x y : ℝ) :
    Summable (fun n => kernelTerm m n t x y) :=
  (heatMajorant_summable ht m 0).of_norm_bounded (fun n => kernelTerm_bound m n ht x y)

theorem kernelTerm_mul_integrable (m n : ℕ) {t : ℝ} (ht : 0<t) (x : ℝ)
    {g : ℝ→ℝ} (hg : Integrable g intervalMeasure) :
    Integrable (fun y => kernelTerm m n t x y*g y) intervalMeasure := by
  have hc : Continuous (kernelTerm m n t x) :=
    continuous_const.mul (normalizedFunction_contDiff m n).continuous
  exact hg.bdd_mul hc.aestronglyMeasurable (ae_of_all _ (kernelTerm_bound m n ht x))

theorem kernel_integral_tsum (m : ℕ) {t : ℝ} (ht : 0<t) (x : ℝ)
    {g : ℝ→ℝ} (hg : Integrable g intervalMeasure) :
    (∫ y,heatKernel m t x y*g y ∂intervalMeasure) =
      ∑'n,∫ y,kernelTerm m n t x y*g y ∂intervalMeasure := by
  have hb (n : ℕ) : (∫ y, ‖kernelTerm m n t x y*g y‖ ∂intervalMeasure) ≤
      heatMajorant m 0 t n*(∫ y,‖g y‖ ∂intervalMeasure) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (kernelTerm_mul_integrable m n ht x hg).norm (hg.norm.const_mul _)
    filter_upwards [] with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (kernelTerm_bound m n ht x y) (norm_nonneg _)
  have hs := ((heatMajorant_summable ht m 0).mul_right (∫ y,‖g y‖ ∂intervalMeasure)).of_nonneg_of_le
    (fun n => integral_nonneg (fun y => norm_nonneg _)) hb
  rw [integral_tsum_of_summable_integral_norm (fun n => kernelTerm_mul_integrable m n ht x hg) hs]
  apply integral_congr_ae
  filter_upwards [] with y
  change (∑'n,kernelTerm m n t x y)*g y = ∑'n,kernelTerm m n t x y*g y
  exact tsum_mul_right.symm

theorem normalizedFunction_inner (m n j : ℕ) (hm : 0<m) :
    (∫ y,normalizedFunction m n y*normalizedFunction m j y ∂intervalMeasure) =
      if n=j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (normalizedVector_orthonormal hm) n j
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [normalizedVector_ae_eq m n,normalizedVector_ae_eq m j] with y hn hj
  simp only [hn,hj,RCLike.inner_apply,conj_trivial]
  ring

/-- The complete true heat kernel acts diagonally on each actual normalized eigenfunction. -/
theorem heatKernel_eigenfunction (m j : ℕ) (hm : 0<m) {t : ℝ} (ht : 0<t) (x : ℝ) :
    (∫ y,heatKernel m t x y*normalizedFunction m j y ∂intervalMeasure) =
      Real.exp (-t*eigenvalue m j)*normalizedFunction m j x := by
  have hg : Integrable (normalizedFunction m j) intervalMeasure :=
    ((eigenfunction_memLp m j).integrable (by norm_num)).const_mul _
  rw [kernel_integral_tsum m ht x hg]
  have he (n : ℕ) : (∫ y,kernelTerm m n t x y*normalizedFunction m j y ∂intervalMeasure) =
      if n=j then Real.exp (-t*eigenvalue m j)*normalizedFunction m j x else 0 := by
    simp only [kernelTerm,mul_assoc,integral_const_mul,normalizedFunction_inner m n j hm]
    split_ifs with hn
    · subst n; ring
    · ring
  simp_rw [he]
  simp

/-- The full heat kernel and the finite spectral evolution agree on finite initial data. -/
theorem heatKernel_finiteHeat_initial (m : ℕ) (hm : 0<m) (F : Finset ℕ) (c : ℕ→ℝ)
    {t : ℝ} (ht : 0<t) (x : ℝ) :
    (∫y,heatKernel m t x y*finiteHeat m F c 0 y ∂intervalMeasure) = finiteHeat m F c t x := by
  have hi (n : ℕ) : Integrable (fun y => c n*(heatKernel m t x y*normalizedFunction m n y))
      intervalMeasure :=
    ((continuous_const.mul ((heatKernel_continuous_right m ht x).mul
      (normalizedFunction_contDiff m n).continuous)).continuousOn.integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  simp_rw [finiteHeat_zero_time]
  calc
    (∫y,heatKernel m t x y*(∑n∈F,c n*normalizedFunction m n y) ∂intervalMeasure) =
        ∫y,∑n∈F,c n*(heatKernel m t x y*normalizedFunction m n y) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _=∑n∈F,c n*(∫y,heatKernel m t x y*normalizedFunction m n y ∂intervalMeasure) := by
      rw [integral_finset_sum F (fun n hn => hi n)]
      simp only [integral_const_mul]
    _=finiteHeat m F c t x := by
      unfold finiteHeat
      apply Finset.sum_congr rfl
      intro n hn
      rw [heatKernel_eigenfunction m n hm ht x]
      ring

/-- The concrete angular polynomial is the actual initial function for the kernel action. -/
theorem heatKernel_polynomial (m : ℕ) (hm : 0<m) (p : Polynomial ℝ)
    {t : ℝ} (ht : 0<t) (x : ℝ) :
    (∫y,heatKernel m t x y*angularPolynomial m p y ∂intervalMeasure) = polynomialHeat m p t x := by
  simp_rw [← polynomialHeat_initial m p]
  exact heatKernel_finiteHeat_initial m hm _ _ ht x

#print axioms heatKernel_polynomial
#print axioms kernel_integral_tsum
#print axioms heatKernel_eigenfunction
end Legacy.BecknerOnofri.JacobiHeatPositivity

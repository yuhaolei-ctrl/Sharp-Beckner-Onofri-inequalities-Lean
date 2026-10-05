module

public import Legacy.BecknerOnofri.JacobiTensorKernel
public import Legacy.BecknerOnofri.JacobiHeatSmooth

@[expose] public section

/-! The actual product of the one-dimensional Jacobi heat kernels,
with the heat parameter `exp(-t*lambda)` in every coordinate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace Legacy.BecknerOnofri.JacobiTensorHeatKernel
open JacobiTensor JacobiEigenfunctions

/-- Absolute summability of a finite product of independently indexed scalar families. -/
theorem summable_norm_pi_product {d : ℕ} (f : Fin d → ℕ → ℝ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun n : Index d => ‖∏ i, f i (n i)‖) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    have hh := (hf 0).mul_norm (ih (fun i => f i.succ) (fun i => hf i.succ))
    apply (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).summable_iff.mp
    simpa only [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ] using hh

theorem prod_tsum_eq {d : ℕ} (f : Fin d → ℕ → ℝ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    (∏ i, ∑' n : ℕ, f i n) = ∑' n : Index d, ∏ i, f i (n i) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.prod_univ_succ, ih (fun i => f i.succ) (fun i => hf i.succ)]
    rw [tsum_mul_tsum_of_summable_norm (hf 0)
      (summable_norm_pi_product (fun i => f i.succ) (fun i => hf i.succ))]
    simpa only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      using (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).tsum_eq
        (fun n : Index (d+1) => ∏ i, f i (n i))

def oneTerm (m : ℕ) (t : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  Real.exp (-t*eigenvalue m n)*normalizedFunction m n x*normalizedFunction m n y

theorem oneTerm_bound (m : ℕ) (t : ℝ) (n : ℕ) (x y : ℝ) :
    ‖oneTerm m t n x y‖ ≤ JacobiHeatBounds.heatMajorant m 0 t n := by
  have h := JacobiHeatBounds.heatTerm_derivative_bound (ε := t) m n 0
    (z := ![t,x,y]) (by simp [JacobiHeatBounds.timeSlab])
  rw [norm_iteratedFDeriv_zero] at h
  have he : JacobiHeatBounds.heatTerm m n ![t,x,y] = oneTerm m t n x y := by
    simp only [JacobiHeatBounds.heatTerm, Fin.prod_univ_three, JacobiHeatBounds.heatFactor]
    simp only [ite_true, if_neg (show (1 : Fin 3) ≠ 0 by decide),
      if_neg (show (2 : Fin 3) ≠ 0 by decide)]
    change Real.exp (-(eigenvalue m n)*t)*normalizedFunction m n x*normalizedFunction m n y = _
    simp only [oneTerm]
    rw [show -(eigenvalue m n)*t = -t*eigenvalue m n by ring]
  rwa [he] at h

theorem oneMajorant_nonneg (m : ℕ) (t : ℝ) (n : ℕ) :
    0 ≤ JacobiHeatBounds.heatMajorant m 0 t n :=
  (norm_nonneg _).trans (oneTerm_bound m t n 0 0)

theorem oneTerm_norm_summable (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun n => ‖oneTerm m t n x y‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => oneTerm_bound m t n x y)
    (JacobiHeatBounds.heatMajorant_summable ht m 0)

def kernel {d : ℕ} (a : Index d) (t : ℝ) (x y : Space d) : ℝ :=
  ∏ i, JacobiHeatBounds.heatKernel (a i) t (x i) (y i)

def term {d : ℕ} (a : Index d) (t : ℝ) (n : Index d) (z : Space d × Space d) : ℝ :=
  Real.exp (-t*tensorEigenvalue a n)*tensorFunction a n z.1*tensorFunction a n z.2

def majorant {d : ℕ} (a : Index d) (t : ℝ) (n : Index d) : ℝ :=
  ∏ i, JacobiHeatBounds.heatMajorant (a i) 0 t (n i)

theorem term_eq_product {d : ℕ} (a n : Index d) (t : ℝ) (x y : Space d) :
    term a t n (x,y) = ∏ i, oneTerm (a i) t (n i) (x i) (y i) := by
  simp only [term, oneTerm, tensorFunction, Finset.prod_mul_distrib, tensorEigenvalue]
  rw [← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]

theorem term_bound {d : ℕ} (a : Index d) (t : ℝ) (n : Index d) (z : Space d × Space d) :
    ‖term a t n z‖ ≤ majorant a t n := by
  rw [show z = (z.1,z.2) from rfl, term_eq_product, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun i _ => oneTerm_bound (a i) t (n i) (z.1 i) (z.2 i))

theorem majorant_nonneg {d : ℕ} (a : Index d) (t : ℝ) (n : Index d) : 0 ≤ majorant a t n :=
  Finset.prod_nonneg (fun i _ => oneMajorant_nonneg (a i) t (n i))

theorem majorant_summable {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) : Summable (majorant a t) := by
  have h := summable_norm_pi_product (fun i n => JacobiHeatBounds.heatMajorant (a i) 0 t n)
    (fun i => (JacobiHeatBounds.heatMajorant_summable ht (a i) 0).norm)
  change Summable (fun n => ‖majorant a t n‖) at h
  simpa only [Real.norm_of_nonneg (majorant_nonneg a t _)] using h

theorem term_norm_summable {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    Summable (fun n => ‖term a t n (x,y)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_bound a t n (x,y))
    (majorant_summable a ht)

theorem kernel_series {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    kernel a t x y = ∑' n : Index d, term a t n (x,y) := by
  unfold kernel JacobiHeatBounds.heatKernel
  change (∏ i, ∑' n, oneTerm (a i) t n (x i) (y i)) = _
  rw [prod_tsum_eq _ (fun i => oneTerm_norm_summable (a i) ht (x i) (y i))]
  apply tsum_congr
  intro n
  exact (term_eq_product a n t x y).symm

theorem term_continuous {d : ℕ} (a n : Index d) (t : ℝ) : Continuous (term a t n) :=
  (continuous_const.mul ((tensorFunction_continuous a n).comp continuous_fst)).mul
    ((tensorFunction_continuous a n).comp continuous_snd)

def termBCF {d : ℕ} (a : Index d) (t : ℝ) (n : Index d) : (Space d × Space d) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (term a t n) (term_continuous a n t)
    (majorant a t n) (term_bound a t n)

theorem termBCF_norm_le {d : ℕ} (a : Index d) (t : ℝ) (n : Index d) :
    ‖termBCF a t n‖ ≤ majorant a t n :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le (term_continuous a n t)
    (majorant_nonneg a t n) (term_bound a t n)

theorem termBCF_summable {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    Summable (termBCF a t) :=
  (majorant_summable a ht).of_norm_bounded (termBCF_norm_le a t)

def kernelBCF {d : ℕ} (a : Index d) (t : ℝ) : (Space d × Space d) →ᵇ ℝ :=
  ∑' n : Index d, termBCF a t n

theorem kernelBCF_apply {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (z : Space d × Space d) :
    kernelBCF a t z = kernel a t z.1 z.2 := by
  rw [kernel_series a ht]
  exact (BoundedContinuousFunction.evalCLM ℝ z).map_tsum (termBCF_summable a ht)

theorem kernel_continuous {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    Continuous (fun z : Space d × Space d => kernel a t z.1 z.2) := by
  convert (kernelBCF a t).continuous using 1
  funext z
  exact (kernelBCF_apply a ht z).symm

theorem termBCF_toLp {d : ℕ} (a n : Index d) (t : ℝ) :
    BoundedContinuousFunction.toLp 2 ((JacobiTensor.measure d).prod (JacobiTensor.measure d)) ℝ
      (termBCF a t n) = Real.exp (-t*tensorEigenvalue a n) •
        SpectralKernel.tensor (JacobiTensor.measure d) (tensorVector a n) (tensorVector a n) := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 _ ℝ (termBCF a t n),
    Lp.coeFn_smul (Real.exp (-t*tensorEigenvalue a n))
      (SpectralKernel.tensor (JacobiTensor.measure d) (tensorVector a n) (tensorVector a n)),
    SpectralKernel.tensor_coe (JacobiTensor.measure d) (tensorVector a n) (tensorVector a n),
    Measure.quasiMeasurePreserving_fst.ae (tensorVector_ae_eq a n),
    Measure.quasiMeasurePreserving_snd.ae (tensorVector_ae_eq a n)] with z hz hs he h1 h2
  rw [hz, hs, Pi.smul_apply, smul_eq_mul, he, h1, h2]
  change Real.exp (-t*tensorEigenvalue a n)*tensorFunction a n z.1*tensorFunction a n z.2 = _
  ring

theorem heatCoefficient_eq_product {d : ℕ} (a n : Index d) (t : ℝ) :
    Real.exp (-t*tensorEigenvalue a n) = ∏ i, Real.exp (-t*eigenvalue (a i) (n i)) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [tensorEigenvalue, Finset.mul_sum]

theorem heatCoefficient_summable {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => Real.exp (-t*tensorEigenvalue a n)) := by
  have h : ∀ i : Fin d, Summable (fun n => ‖Real.exp (-t*eigenvalue (a i) n)‖) := by
    intro i
    simpa only [pow_zero, one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      using JacobiHeatBounds.shifted_polynomial_gaussian_summable ht (a i) 0
  have hh := summable_norm_pi_product _ h
  simpa only [← heatCoefficient_eq_product, Real.norm_of_nonneg (Real.exp_nonneg _)] using hh

theorem heatCoefficient_sq_summable {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => (Real.exp (-t*tensorEigenvalue a n))^2) := by
  apply (heatCoefficient_summable a (t := 2*t) (by positivity)).congr
  intro n
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem kernelBCF_toLp {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    BoundedContinuousFunction.toLp 2 ((JacobiTensor.measure d).prod (JacobiTensor.measure d)) ℝ
      (kernelBCF a t) = SpectralKernel.spectralKernel (JacobiTensor.measure d) (hilbertBasis a)
        (fun n => Real.exp (-t*tensorEigenvalue a n)) := by
  rw [kernelBCF, ContinuousLinearMap.map_tsum _ (termBCF_summable a ht)]
  simp_rw [termBCF_toLp]
  simpa only [JacobiTensor.hilbertBasis_apply] using
    (SpectralKernel.spectralKernel_hasSum (JacobiTensor.measure d) (hilbertBasis a)
      (fun n => Real.exp (-t*tensorEigenvalue a n)) (heatCoefficient_sq_summable a ht)).tsum_eq

theorem spectralKernel_ae_kernel {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    (SpectralKernel.spectralKernel (JacobiTensor.measure d) (hilbertBasis a)
      (fun n => Real.exp (-t*tensorEigenvalue a n)) : Space d × Space d → ℝ)
      =ᵐ[(JacobiTensor.measure d).prod (JacobiTensor.measure d)] fun z => kernel a t z.1 z.2 := by
  rw [← kernelBCF_toLp a ht]
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 _ ℝ (kernelBCF a t)] with z hz
  exact hz.trans (kernelBCF_apply a ht z)

/-- The heat diagonal also covers the zero multi-index, with its constant Neumann mode. -/
def heatSymbol {d : ℕ} (a : Index d) (t : ℝ) : SpectralHeatInverse.Symbol (Index d) :=
  SpectralHeatInverse.boundedSymbol (fun n => Real.exp (-(max t 0)*tensorEigenvalue a n)) 1 (by
    intro n
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _))
      (tensorEigenvalue_nonneg a n))

def heatOperator {d : ℕ} (a : Index d) (t : ℝ) : TensorL2 d →L[ℝ] TensorL2 d :=
  SpectralHeatInverse.diagonal (hilbertBasis a) (heatSymbol a t)

theorem heatOperator_eq_heat {d : ℕ} (a : Index d) (ha : a ≠ 0) (t : ℝ) :
    heatOperator a t = JacobiTensorSpectrum.heat a ha t := rfl

theorem kernel_representation {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (u : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => kernel a t x y*u y) (JacobiTensor.measure d) ∧
        (∫ y, kernel a t x y*u y ∂JacobiTensor.measure d) = heatOperator a t u x := by
  have hc : ∀ n, heatSymbol a t n = Real.exp (-t*tensorEigenvalue a n) := by
    intro n
    change Real.exp (-(max t 0)*tensorEigenvalue a n) = _
    rw [max_eq_left ht.le]
  have hsq : Summable (fun n => (heatSymbol a t n)^2) := by
    simpa only [hc] using heatCoefficient_sq_summable a ht
  have hh := SpectralKernel.spectralKernel_representation (JacobiTensor.measure d)
    (hilbertBasis a) (heatSymbol a t) hsq u
  have he := Measure.ae_ae_of_ae_prod (spectralKernel_ae_kernel a ht)
  have hcf : (heatSymbol a t : Index d → ℝ) = fun n => Real.exp (-t*tensorEigenvalue a n) := funext hc
  rw [hcf] at hh
  filter_upwards [hh, he] with x hx he
  have hm : (fun y => SpectralKernel.spectralKernel (JacobiTensor.measure d) (hilbertBasis a)
      (fun n => Real.exp (-t*tensorEigenvalue a n)) (x,y)*u y)
      =ᵐ[JacobiTensor.measure d] fun y => kernel a t x y*u y := by
    filter_upwards [he] with y hy
    rw [hy]
  exact ⟨hx.1.congr hm, (integral_congr_ae hm).symm.trans hx.2⟩

theorem kernel_representation_positive {d : ℕ} (a : Index d) (ha : a ≠ 0)
    {t : ℝ} (ht : 0 < t) (u : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => kernel a t x y*u y) (JacobiTensor.measure d) ∧
        (∫ y, kernel a t x y*u y ∂JacobiTensor.measure d) = JacobiTensorSpectrum.heat a ha t u x := by
  simpa only [heatOperator_eq_heat a ha] using kernel_representation a ht u

theorem kernel_symm {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    kernel a t x y = kernel a t y x := by
  rw [kernel_series a ht, kernel_series a ht]
  apply tsum_congr
  intro n
  simp only [term]
  ring

theorem kernel_norm_le {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    ‖kernel a t x y‖ ≤ ∑' n : Index d, majorant a t n := by
  rw [kernel_series a ht]
  exact (norm_tsum_le_tsum_norm (term_norm_summable a ht x y)).trans
    (Summable.tsum_le_tsum (fun n => term_bound a t n (x,y))
      (term_norm_summable a ht x y) (majorant_summable a ht))

#print axioms kernel_series
#print axioms spectralKernel_ae_kernel
#print axioms kernel_representation
end Legacy.BecknerOnofri.JacobiTensorHeatKernel

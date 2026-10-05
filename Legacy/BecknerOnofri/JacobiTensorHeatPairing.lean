module

public import Legacy.BecknerOnofri.JacobiTensorHeatComparison
public import Legacy.BecknerOnofri.PositiveKernelComparison

@[expose] public section

/-! Actual product heat pairings and the spectral-gap L1 bound used for Mellin inversion. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorHeatKernel
open JacobiTensor

/-- Joint measurability uses the actual countable spectral series, including at nonpositive times. -/
theorem kernel_joint_measurable {d : ℕ} (a : Index d) :
    Measurable (fun p : ℝ × (Space d × Space d) => kernel a p.1 p.2.1 p.2.2) := by
  unfold kernel JacobiHeatBounds.heatKernel
  apply Finset.measurable_prod
  intro i _
  apply Measurable.tsum
  intro n
  apply Continuous.measurable
  exact ((Real.continuous_exp.comp (continuous_fst.neg.mul_const _)).mul
    ((JacobiEigenfunctions.normalizedFunction_contDiff (a i) n).continuous.comp
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))).mul
    ((JacobiEigenfunctions.normalizedFunction_contDiff (a i) n).continuous.comp
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))

theorem kernel_pair_integrable {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t)
    (f g : TensorL2 d) :
    Integrable (fun z : Space d × Space d => kernel a t z.1 z.2*f z.1*g z.2)
      ((JacobiTensor.measure d).prod (JacobiTensor.measure d)) := by
  let K := SpectralKernel.spectralKernel (JacobiTensor.measure d) (hilbertBasis a)
    (fun n => Real.exp (-t*tensorEigenvalue a n))
  apply (L2.integrable_inner (𝕜 := ℝ) (SpectralKernel.tensor (JacobiTensor.measure d) f g) K).congr
  filter_upwards [SpectralKernel.tensor_coe (JacobiTensor.measure d) f g,
    spectralKernel_ae_kernel a ht] with z he hk
  simp only [RCLike.inner_apply, conj_trivial, he]
  change K z*(f z.1*g z.2) = _
  rw [show K z = kernel a t z.1 z.2 from hk]
  ring

theorem kernel_pairing {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) (f g : TensorL2 d) :
    (∫ z : Space d × Space d, kernel a t z.1 z.2*f z.1*g z.2
      ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d)) =
      @inner ℝ (TensorL2 d) _ f (heatOperator a t g) := by
  rw [L2.inner_def, integral_prod _ (kernel_pair_integrable a ht f g)]
  apply integral_congr_ae
  filter_upwards [kernel_representation a ht g] with x hx
  simp only [RCLike.inner_apply, conj_trivial, ← hx.2]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

theorem kernel_abs_pair_integral_le {d : ℕ} (a : Index d) (ha : a ≠ 0)
    {t : ℝ} (ht : 0 < t) (f g : TensorL2 d) :
    (∫ z : Space d × Space d, ‖kernel a t z.1 z.2*f z.1*g z.2‖
      ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d)) ≤
      Real.exp (-spectralBottom a*t)*‖f‖*‖g‖ := by
  simp only [Real.norm_eq_abs]
  rw [PositiveKernelRayleigh.integral_abs_pair_eq (JacobiTensor.measure d)
    (kernel_nonnegative_ae a ht), kernel_pairing a ht, heatOperator_eq_heat a ha]
  calc
    _ ≤ ‖(|f| : TensorL2 d)‖*‖JacobiTensorSpectrum.heat a ha t |g|‖ := real_inner_le_norm _ _
    _ ≤ ‖(|f| : TensorL2 d)‖*(Real.exp (-spectralBottom a*t)*‖(|g| : TensorL2 d)‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((JacobiTensorSpectrum.heat a ha t).le_opNorm |g|).trans
        (mul_le_mul_of_nonneg_right (JacobiTensorSpectrum.heat_norm_le a ha ht.le) (norm_nonneg _))
    _ = _ := by simp only [norm_abs_eq_norm]; ring

#print axioms kernel_joint_measurable
#print axioms kernel_abs_pair_integral_le
end Legacy.BecknerOnofri.JacobiTensorHeatKernel

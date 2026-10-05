module

public import Legacy.BecknerOnofri.JacobiTensorMellinKernel
public import Legacy.BecknerOnofri.JacobiTensorHeatStrictComparison

@[expose] public section

/-! Strict comparison survives actual Mellin integration; no inverse-kernel order is assumed. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorMellin
open JacobiTensor

instance timeMeasure_neZero : NeZero timeMeasure := by
  constructor
  intro h
  have hh := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp [timeMeasure] at hh

private theorem integral_strict_mono {f g : ℝ → ℝ} (hf : Integrable f timeMeasure)
    (hg : Integrable g timeMeasure) (hlt : ∀ᵐ t ∂timeMeasure, f t < g t) :
    (∫ t, f t ∂timeMeasure) < ∫ t, g t ∂timeMeasure := by
  have hle : f ≤ᵐ[timeMeasure] g := hlt.mono (fun _ h => h.le)
  have hi := integral_mono_ae hf hg hle
  apply lt_of_le_of_ne hi
  intro he
  have heq := (integral_eq_iff_of_ae_le hf hg hle).mp he
  obtain ⟨t,ht,heqt⟩ := (hlt.and heq).exists
  exact (ne_of_lt ht) heqt

/-- The actual first-index Jacobi inverse kernel is strictly positive almost everywhere. -/
theorem kernel_single_pos_ae {d : ℕ} (i : Fin d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, 0 < kernel (Pi.single i 1) s z := by
  have ha : (Pi.single i 1 : Index d) ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp at hi
  filter_upwards [time_integrable_ae (Pi.single i 1) ha hs,
    Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hz hx hy
  apply mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos hs))
  have hp : ∀ᵐ t ∂timeMeasure, 0 < integrand (Pi.single i 1) s t z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_pos (Real.rpow_pos_of_pos ht _)
      (JacobiTensorHeatKernel.kernel_single_pos i ht hx hy)
  simpa only [Pi.zero_apply, integral_zero] using integral_strict_mono (integrable_zero _ _ _) hz hp

/-- Every higher mixed-index actual inverse kernel is strictly below its first-index baseline. -/
theorem kernel_lt_single_ae {d : ℕ} (a : Index d) (i : Fin d) (hai : 1 ≤ a i)
    (hne : a ≠ Pi.single i 1) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, kernel a s z < kernel (Pi.single i 1) s z := by
  have ha : a ≠ 0 := by
    intro h
    rw [h] at hai
    simp at hai
  have hb : (Pi.single i 1 : Index d) ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp at hi
  filter_upwards [time_integrable_ae a ha hs, time_integrable_ae (Pi.single i 1) hb hs,
    Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hz hzb hx hy
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr (Real.Gamma_pos_of_pos hs))
  apply integral_strict_mono hz hzb
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_lt_mul_of_pos_left
    (JacobiTensorHeatKernel.kernel_lt_single a i hai hne ht hx hy) (Real.rpow_pos_of_pos ht _)

theorem kernel_symmetric {d : ℕ} (a : Index d) (s : ℝ) (z : Space d × Space d) :
    kernel a s z.swap = kernel a s z := by
  unfold kernel
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change t^(s-1)*JacobiTensorHeatKernel.kernel a t z.2 z.1 =
    t^(s-1)*JacobiTensorHeatKernel.kernel a t z.1 z.2
  rw [JacobiTensorHeatKernel.kernel_symm a ht z.2 z.1]

theorem kernel_symmetric_ae {d : ℕ} (a : Index d) (s : ℝ) :
    ∀ᵐ z ∂pairMeasure d, kernel a s z.swap = kernel a s z :=
  ae_of_all _ (kernel_symmetric a s)

theorem inversePower_positive {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    PositiveOperatorNeumann.Positive (JacobiTensor.measure d)
      (JacobiTensorSpectrum.inversePower a ha s hs) :=
  PositiveKernelRayleigh.represented_kernel_positive (JacobiTensor.measure d)
    (JacobiTensorSpectrum.inversePower a ha s hs) (kernel a s) (kernel_nonnegative_ae a hs)
    (fun f => (kernel_representation a ha hs f).mono (fun _ h => h.2.symm))

#print axioms kernel_single_pos_ae
#print axioms kernel_lt_single_ae
#print axioms kernel_symmetric
#print axioms inversePower_positive
end Legacy.BecknerOnofri.JacobiTensorMellin

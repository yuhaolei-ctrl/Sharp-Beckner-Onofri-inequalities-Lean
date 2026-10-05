import Legacy.BecknerOnofri.JacobiTensorMellinIntegrability

/-! The actual nonnegative Mellin kernel of every positive inverse Jacobi tensor power. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorMellin
open JacobiTensor

/-- The integral is over actual positive heat time and the actual tensor heat kernel. -/
def kernel {d : ℕ} (a : Index d) (s : ℝ) (z : Space d × Space d) : ℝ :=
  (Real.Gamma s)⁻¹ * ∫ t : ℝ, integrand a s t z ∂timeMeasure

theorem kernel_aestronglyMeasurable {d : ℕ} (a : Index d) (s : ℝ) :
    AEStronglyMeasurable (kernel a s) (pairMeasure d) :=
  ((integrand_aestronglyMeasurable a s).prod_swap.integral_prod_right').const_mul _

theorem time_integrable_ae {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, Integrable (fun t : ℝ => integrand a s t z) timeMeasure :=
  (integrand_integrable a ha hs).prod_left_ae

theorem kernel_integrable {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    Integrable (kernel a s) (pairMeasure d) :=
  (integrand_integrable a ha hs).integral_prod_right.const_mul _

theorem kernel_nonnegative {d : ℕ} (a : Index d) {s : ℝ} (hs : 0 < s)
    {z : Space d × Space d} (hx : ∀ i, z.1 i ∈ Icc 0 Real.pi)
    (hy : ∀ i, z.2 i ∈ Icc 0 Real.pi) : 0 ≤ kernel a s z := by
  apply mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos hs).le)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _)
    (JacobiTensorHeatKernel.kernel_nonnegative a ht hx hy)

theorem kernel_nonnegative_ae {d : ℕ} (a : Index d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, 0 ≤ kernel a s z := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hx hy
  exact kernel_nonnegative a hs (fun i => ⟨(hx i).1.le,(hx i).2.le⟩)
    (fun i => ⟨(hy i).1.le,(hy i).2.le⟩)

theorem kernel_pair_integrable {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    Integrable (fun z : Space d × Space d => kernel a s z*f z.1*g z.2) (pairMeasure d) := by
  convert (weighted_pair_integrable a ha hs f g).integral_prod_right.const_mul (Real.Gamma s)⁻¹ using 1
  funext z
  simp only [integral_mul_const, kernel]
  ring

theorem kernel_pairing {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    (∫ z : Space d × Space d, kernel a s z*f z.1*g z.2 ∂pairMeasure d) =
      @inner ℝ (TensorL2 d) _ f (JacobiTensorSpectrum.inversePower a ha s hs g) := by
  have hI := weighted_pair_integrable a ha hs f g
  calc
    _ = (Real.Gamma s)⁻¹ * ∫ z : Space d × Space d,
        ∫ t : ℝ, integrand a s t z*f z.1*g z.2 ∂timeMeasure ∂pairMeasure d := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by simp only [integral_mul_const, kernel]; ring)
    _ = (Real.Gamma s)⁻¹ * ∫ t : ℝ,
        ∫ z : Space d × Space d, integrand a s t z*f z.1*g z.2 ∂pairMeasure d ∂timeMeasure := by
      congr 1
      exact integral_integral_swap hI.swap
    _ = (Real.Gamma s)⁻¹ * ∫ t : ℝ,
        (innerSL ℝ f) (t^(s-1) • JacobiTensorSpectrum.heat a ha t g) ∂timeMeasure := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have he : (fun z : Space d × Space d => integrand a s t z*f z.1*g z.2) =
          fun z => t^(s-1)*(JacobiTensorHeatKernel.kernel a t z.1 z.2*f z.1*g z.2) := by
        funext z
        simp only [integrand]
        ring
      rw [he, integral_const_mul, JacobiTensorHeatKernel.kernel_pairing a ht,
        JacobiTensorHeatKernel.heatOperator_eq_heat a ha]
      simp only [innerSL_apply_apply, inner_smul_right]
    _ = @inner ℝ (TensorL2 d) _ f
        ((Real.Gamma s)⁻¹ • ∫ t : ℝ, t^(s-1) • JacobiTensorSpectrum.heat a ha t g ∂timeMeasure) := by
      rw [(innerSL ℝ f).integral_comp_comm (JacobiTensorSpectrum.heat_integrable a ha hs g),
        inner_smul_right]
      rfl
    _ = _ := by rw [JacobiTensorSpectrum.heat_integral_eq_inversePower a ha hs g]

theorem kernel_action_integrable {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    Integrable (fun z : Space d × Space d => kernel a s z*g z.2) (pairMeasure d) := by
  apply (kernel_pair_integrable a ha hs (constantOne d) g).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (constantOne_ae d)] with z hz
  simp only [hz, mul_one]

/-- Every actual L2 input has an almost everywhere integrable Mellin-kernel slice. -/
theorem kernel_action_slices {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => kernel a s (x,y)*g y) (JacobiTensor.measure d) :=
  (kernel_action_integrable a ha hs g).prod_right_ae

theorem integral_pair_eq_iterated {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    (∫ z : Space d × Space d, kernel a s z*f z.1*g z.2 ∂pairMeasure d) =
      ∫ x, f x*(∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) ∂JacobiTensor.measure d := by
  rw [integral_prod _ (kernel_pair_integrable a ha hs f g)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

/-- The actual Mellin integral represents the actual inverse operator on every L2 input. -/
theorem kernel_represents {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    (fun x => ∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) =ᵐ[JacobiTensor.measure d]
      JacobiTensorSpectrum.inversePower a ha s hs g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (kernel_action_integrable a ha hs g).integral_prod_left
    ((Lp.memLp (JacobiTensorSpectrum.inversePower a ha s hs g)).integrable (by norm_num))
  intro v hv hμv
  let f : TensorL2 d := indicatorConstLp 2 hv hμv.ne (1:ℝ)
  rw [← L2.inner_indicatorConstLp_one hv hμv.ne (JacobiTensorSpectrum.inversePower a ha s hs g)]
  change (∫ x in v, ∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d ∂JacobiTensor.measure d) =
    @inner ℝ (TensorL2 d) _ f (JacobiTensorSpectrum.inversePower a ha s hs g)
  rw [← kernel_pairing a ha hs f g, integral_pair_eq_iterated a ha hs f g, ← integral_indicator hv]
  apply integral_congr_ae
  filter_upwards [@indicatorConstLp_coeFn (Space d) _ _ 2 (JacobiTensor.measure d) _
    v hv hμv.ne (1:ℝ)] with x hx
  change v.indicator (fun x => ∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) x =
    f x*(∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d)
  change indicatorConstLp 2 hv hμv.ne (1:ℝ) x = _ at hx
  rw [show f x = v.indicator (fun _ => (1:ℝ)) x from hx]
  by_cases hxv : x ∈ v <;> simp [hxv]

theorem kernel_representation {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => kernel a s (x,y)*g y) (JacobiTensor.measure d) ∧
        (∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) =
          JacobiTensorSpectrum.inversePower a ha s hs g x :=
  (kernel_action_slices a ha hs g).and (kernel_represents a ha hs g)

#print axioms kernel_integrable
#print axioms kernel_pairing
#print axioms kernel_representation
end Legacy.BecknerOnofri.JacobiTensorMellin

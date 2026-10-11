module

public import BecknerOnofri.V2.Reaudit.HeatKernel.TensorWiring
public import Legacy.BecknerOnofri.JacobiTensorMellinComparison
public import Legacy.BecknerOnofri.JacobiTensorHeatPairing

@[expose] public section

/-! # Integrability and kernel representation of the Mellin kernels on the new heat-kernel inputs
(U05/S015)

Verbatim re-proofs (statement-identical; the only change is that the nonnegativity of the tensor
heat kernel is taken from `TensorWiring.kernel_nonnegative_V2`, i.e. from the resolvent-comparison
route, instead of the legacy parabolic maximum principle) of

* `JacobiTensorHeatKernel.kernel_abs_pair_integral_le`,
* `JacobiTensorMellin.weighted_pair_integrable`, `integrand_integrable`, `time_integrable_ae`,
  `kernel_pair_integrable`, `kernel_pairing`, `kernel_action_integrable`, `kernel_action_slices`,
  `integral_pair_eq_iterated`, `kernel_represents`, `kernel_representation`,
  `kernel_single_pos_ae`.
-/

noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Wiring

open Legacy.BecknerOnofri
open Legacy.BecknerOnofri.JacobiTensor

theorem kernel_nonnegative_ae_V2 {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ z ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d),
      0 ≤ JacobiTensorHeatKernel.kernel a t z.1 z.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hx hy
  exact kernel_nonnegative_V2 a ht (fun i => ⟨(hx i).1.le, (hx i).2.le⟩)
    (fun i => ⟨(hy i).1.le, (hy i).2.le⟩)

section HeatLevel
open Legacy.BecknerOnofri.JacobiTensorHeatKernel
open Legacy.BecknerOnofri.JacobiTensorMellin hiding kernel

theorem kernel_abs_pair_integral_le_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0)
    {t : ℝ} (ht : 0 < t) (f g : TensorL2 d) :
    (∫ z : Space d × Space d, ‖kernel a t z.1 z.2*f z.1*g z.2‖
      ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d)) ≤
      Real.exp (-spectralBottom a*t)*‖f‖*‖g‖ := by
  simp only [Real.norm_eq_abs]
  rw [PositiveKernelRayleigh.integral_abs_pair_eq (JacobiTensor.measure d)
    (kernel_nonnegative_ae_V2 a ht), kernel_pairing a ht, heatOperator_eq_heat a ha]
  calc
    _ ≤ ‖(|f| : TensorL2 d)‖*‖JacobiTensorSpectrum.heat a ha t |g|‖ := real_inner_le_norm _ _
    _ ≤ ‖(|f| : TensorL2 d)‖*(Real.exp (-spectralBottom a*t)*‖(|g| : TensorL2 d)‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((JacobiTensorSpectrum.heat a ha t).le_opNorm |g|).trans
        (mul_le_mul_of_nonneg_right (JacobiTensorSpectrum.heat_norm_le a ha ht.le) (norm_nonneg _))
    _ = _ := by simp only [norm_abs_eq_norm]; ring

/-- Positivity moves both absolute values to the L2 inputs; the heat norm supplies the time
majorant. -/
theorem weighted_pair_integrable_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    Integrable (fun p : ℝ × (Space d × Space d) => integrand a s p.1 p.2*f p.2.1*g p.2.2)
      (timeMeasure.prod (pairMeasure d)) := by
  apply (integrable_prod_iff (weighted_pair_aestronglyMeasurable a s f g)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    convert (kernel_pair_integrable a ht f g).const_mul (t^(s-1)) using 1
    funext z
    simp only [integrand]
    ring
  · apply (((gamma_majorant_integrable a ha hs).mul_const ‖f‖).mul_const ‖g‖).mono'
      (weighted_pair_aestronglyMeasurable a s f g).norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : 0 ≤ t^(s-1) := Real.rpow_nonneg ht.le _
    have he : (fun z : Space d × Space d => ‖integrand a s t z*f z.1*g z.2‖) =
        fun z => t^(s-1)*‖kernel a t z.1 z.2*f z.1*g z.2‖ := by
      funext z
      simp only [integrand, show t^(s-1)*kernel a t z.1 z.2*f z.1*g z.2 =
        t^(s-1)*(kernel a t z.1 z.2*f z.1*g z.2) by ring,
        norm_mul, Real.norm_of_nonneg hp]
    rw [he, integral_const_mul, Real.norm_of_nonneg (mul_nonneg hp (integral_nonneg (fun _ => norm_nonneg _)))]
    exact (mul_le_mul_of_nonneg_left (kernel_abs_pair_integral_le_V2 a ha ht f g) hp).trans_eq (by ring)

/-- The genuine heat kernel is integrable jointly over both spatial variables and Mellin time. -/
theorem integrand_integrable_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × (Space d × Space d) => integrand a s p.1 p.2)
      (timeMeasure.prod (pairMeasure d)) := by
  apply (weighted_pair_integrable_V2 a ha hs (constantOne d) (constantOne d)).congr
  have hf : ∀ᵐ z ∂pairMeasure d, constantOne d z.1 = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (constantOne_ae d)
  have hg : ∀ᵐ z ∂pairMeasure d, constantOne d z.2 = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (constantOne_ae d)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hf,
    Measure.quasiMeasurePreserving_snd.ae hg] with p hp hq
  simp only [hp,hq,mul_one]

end HeatLevel

section MellinLevel
open Legacy.BecknerOnofri.JacobiTensorMellin

theorem time_integrable_ae_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, Integrable (fun t : ℝ => integrand a s t z) timeMeasure :=
  (integrand_integrable_V2 a ha hs).prod_left_ae

theorem kernel_pair_integrable_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    Integrable (fun z : Space d × Space d => kernel a s z*f z.1*g z.2) (pairMeasure d) := by
  convert (weighted_pair_integrable_V2 a ha hs f g).integral_prod_right.const_mul (Real.Gamma s)⁻¹ using 1
  funext z
  simp only [integral_mul_const, kernel]
  ring

theorem kernel_pairing_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    (∫ z : Space d × Space d, kernel a s z*f z.1*g z.2 ∂pairMeasure d) =
      @inner ℝ (TensorL2 d) _ f (JacobiTensorSpectrum.inversePower a ha s hs g) := by
  have hI := weighted_pair_integrable_V2 a ha hs f g
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

theorem kernel_action_integrable_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    Integrable (fun z : Space d × Space d => kernel a s z*g z.2) (pairMeasure d) := by
  apply (kernel_pair_integrable_V2 a ha hs (constantOne d) g).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (constantOne_ae d)] with z hz
  simp only [hz, mul_one]

/-- Every actual L2 input has an almost everywhere integrable Mellin-kernel slice. -/
theorem kernel_action_slices_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => kernel a s (x,y)*g y) (JacobiTensor.measure d) :=
  (kernel_action_integrable_V2 a ha hs g).prod_right_ae

theorem integral_pair_eq_iterated_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (f g : TensorL2 d) :
    (∫ z : Space d × Space d, kernel a s z*f z.1*g z.2 ∂pairMeasure d) =
      ∫ x, f x*(∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) ∂JacobiTensor.measure d := by
  rw [integral_prod _ (kernel_pair_integrable_V2 a ha hs f g)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

/-- The actual Mellin integral represents the actual inverse operator on every L2 input. -/
theorem kernel_represents_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    (fun x => ∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) =ᵐ[JacobiTensor.measure d]
      JacobiTensorSpectrum.inversePower a ha s hs g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (kernel_action_integrable_V2 a ha hs g).integral_prod_left
    ((Lp.memLp (JacobiTensorSpectrum.inversePower a ha s hs g)).integrable (by norm_num))
  intro v hv hμv
  let f : TensorL2 d := indicatorConstLp 2 hv hμv.ne (1:ℝ)
  rw [← L2.inner_indicatorConstLp_one hv hμv.ne (JacobiTensorSpectrum.inversePower a ha s hs g)]
  change (∫ x in v, ∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d ∂JacobiTensor.measure d) =
    @inner ℝ (TensorL2 d) _ f (JacobiTensorSpectrum.inversePower a ha s hs g)
  rw [← kernel_pairing_V2 a ha hs f g, integral_pair_eq_iterated_V2 a ha hs f g, ← integral_indicator hv]
  apply integral_congr_ae
  filter_upwards [@indicatorConstLp_coeFn (Space d) _ _ 2 (JacobiTensor.measure d) _
    v hv hμv.ne (1:ℝ)] with x hx
  change v.indicator (fun x => ∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) x =
    f x*(∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d)
  change indicatorConstLp 2 hv hμv.ne (1:ℝ) x = _ at hx
  rw [show f x = v.indicator (fun _ => (1:ℝ)) x from hx]
  by_cases hxv : x ∈ v <;> simp [hxv]

theorem kernel_representation_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (g : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => kernel a s (x,y)*g y) (JacobiTensor.measure d) ∧
        (∫ y, kernel a s (x,y)*g y ∂JacobiTensor.measure d) =
          JacobiTensorSpectrum.inversePower a ha s hs g x :=
  (kernel_action_slices_V2 a ha hs g).and (kernel_represents_V2 a ha hs g)

/-- The actual first-index Jacobi inverse kernel is strictly positive almost everywhere. -/
theorem kernel_single_pos_ae_V2 {d : ℕ} (i : Fin d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, 0 < kernel (Pi.single i 1) s z := by
  have ha : (Pi.single i 1 : Index d) ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp at hi
  filter_upwards [time_integrable_ae_V2 (Pi.single i 1) ha hs,
    Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hz hx hy
  apply mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos hs))
  have hp : ∀ᵐ t ∂timeMeasure, 0 < integrand (Pi.single i 1) s t z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_pos (Real.rpow_pos_of_pos ht _)
      (JacobiTensorHeatKernel.kernel_single_pos i ht hx hy)
  simpa only [Pi.zero_apply, integral_zero] using integral_strict_mono (integrable_zero _ _ _) hz hp

end MellinLevel

end BecknerOnofri.V2.Reaudit.HeatKernel.Wiring

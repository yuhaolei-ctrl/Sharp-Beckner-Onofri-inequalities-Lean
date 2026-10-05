module

public import Legacy.BecknerOnofri.JacobiTensorHeatPairing

@[expose] public section

/-! Mellin integrability from actual heat positivity and the spectral gap. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorMellin
open JacobiTensor JacobiTensorHeatKernel

abbrev timeMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev pairMeasure (d : ℕ) := (JacobiTensor.measure d).prod (JacobiTensor.measure d)

def integrand {d : ℕ} (a : Index d) (s : ℝ) (t : ℝ) (z : Space d × Space d) : ℝ :=
  t^(s-1)*kernel a t z.1 z.2

theorem power_aestronglyMeasurable (s : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => t^(s-1)) timeMeasure := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  intro t ht
  exact (Real.continuousAt_rpow_const t (s-1) (Or.inl (ne_of_gt ht))).continuousWithinAt

theorem integrand_aestronglyMeasurable {d : ℕ} (a : Index d) (s : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × (Space d × Space d) => integrand a s p.1 p.2)
      (timeMeasure.prod (pairMeasure d)) :=
  (power_aestronglyMeasurable s).comp_fst.mul (kernel_joint_measurable a).aestronglyMeasurable

theorem weighted_pair_aestronglyMeasurable {d : ℕ} (a : Index d) (s : ℝ) (f g : TensorL2 d) :
    AEStronglyMeasurable
      (fun p : ℝ × (Space d × Space d) => integrand a s p.1 p.2*f p.2.1*g p.2.2)
      (timeMeasure.prod (pairMeasure d)) :=
  ((integrand_aestronglyMeasurable a s).mul
    (Lp.aestronglyMeasurable f).comp_fst.comp_snd).mul
    (Lp.aestronglyMeasurable g).comp_snd.comp_snd

theorem gamma_majorant_integrable {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => t^(s-1)*Real.exp (-spectralBottom a*t)) timeMeasure := by
  apply (GaussianMellinTerm.shifted_integrable hs
      (spectralBottom_pos a (JacobiTensorSpectrum.active_of_ne_zero a ha)) 0).congr
  filter_upwards [] with t
  simp only [sub_zero]
  congr 2
  ring

/-- Positivity moves both absolute values to the L2 inputs; the heat norm supplies the time majorant. -/
theorem weighted_pair_integrable {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
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
    exact (mul_le_mul_of_nonneg_left (kernel_abs_pair_integral_le a ha ht f g) hp).trans_eq (by ring)

def constantOne (d : ℕ) : TensorL2 d := Lp.const 2 (JacobiTensor.measure d) (1:ℝ)

theorem constantOne_ae (d : ℕ) : (constantOne d : Space d → ℝ) =ᵐ[JacobiTensor.measure d] fun _ => 1 :=
  Lp.coeFn_const 2 (JacobiTensor.measure d) (1:ℝ)

/-- The genuine heat kernel is integrable jointly over both spatial variables and Mellin time. -/
theorem integrand_integrable {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × (Space d × Space d) => integrand a s p.1 p.2)
      (timeMeasure.prod (pairMeasure d)) := by
  apply (weighted_pair_integrable a ha hs (constantOne d) (constantOne d)).congr
  have hf : ∀ᵐ z ∂pairMeasure d, constantOne d z.1 = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (constantOne_ae d)
  have hg : ∀ᵐ z ∂pairMeasure d, constantOne d z.2 = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (constantOne_ae d)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hf,
    Measure.quasiMeasurePreserving_snd.ae hg] with p hp hq
  simp only [hp,hq,mul_one]

#print axioms weighted_pair_integrable
#print axioms integrand_integrable
end Legacy.BecknerOnofri.JacobiTensorMellin

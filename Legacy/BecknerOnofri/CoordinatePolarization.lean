import Legacy.BecknerOnofri.CoordinateReflection
import Legacy.BecknerOnofri.ExponentialPartitionContinuity

/-! Genuine half-circle max/min polarization preserves every integrable scalar distributional statistic. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.CoordinatePolarization
attribute [local instance] Classical.propDecidable

def polarize {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  if x ∈ halfTorus i a then max (f x) (f (reflection i a x)) else min (f x) (f (reflection i a x))

theorem polarize_value_or_reflected {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) (x : Torus d) :
    polarize i a f x = f x ∨ polarize i a f x = f (reflection i a x) := by
  unfold polarize
  split_ifs <;> rcases le_total (f x) (f (reflection i a x)) with h | h <;> simp [h]

theorem polarize_pair {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) (Φ : ℝ → ℝ) (x : Torus d) :
    Φ (polarize i a f x)+Φ (polarize i a f (reflection i a x)) = Φ (f x)+Φ (f (reflection i a x)) := by
  rcases reflection_half_or_fixed i a x with hfix | hside
  · simp [polarize, hfix]
  · unfold polarize
    rw [reflection_involutive i a x]
    by_cases hx : x ∈ halfTorus i a
    · have hr : reflection i a x ∉ halfTorus i a := by simpa [hx] using hside
      simp only [if_pos hx, if_neg hr]
      rcases le_total (f x) (f (reflection i a x)) with hf | hf <;>
        simp [hf, add_comm]
    · have hr : reflection i a x ∈ halfTorus i a := hside.mpr hx
      simp only [if_neg hx, if_pos hr]
      rcases le_total (f x) (f (reflection i a x)) with hf | hf <;>
        simp [hf, add_comm]

theorem polarize_measurable {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ} (hf : Measurable f) :
    Measurable (polarize i a f) := by
  have hr := hf.comp (reflection_continuous i a).measurable
  exact (hf.max hr).piecewise (halfTorus_measurable i a) (hf.min hr)

theorem polarize_aestronglyMeasurable {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (torusMeasure d)) : AEStronglyMeasurable (polarize i a f) (torusMeasure d) := by
  have hr := hf.comp_measurePreserving (reflection_measurePreserving i a)
  exact AEStronglyMeasurable.piecewise (halfTorus_measurable i a)
    ((hf.aemeasurable.max hr.aemeasurable).aestronglyMeasurable.restrict)
    ((hf.aemeasurable.min hr.aemeasurable).aestronglyMeasurable.restrict)

theorem reflection_integrable {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) : Integrable (fun x => f (reflection i a x)) (torusMeasure d) :=
  ((reflection_measurePreserving i a).integrable_comp hf.aestronglyMeasurable).mpr hf

theorem reflection_integral {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) :
    (∫ x, f (reflection i a x) ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d :=
  (reflection_measurePreserving i a).integral_comp (reflectionEquiv i a).measurableEmbedding f

theorem polarize_transform_integrable {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (torusMeasure d)) {Φ : ℝ → ℝ} (hΦ : Measurable Φ)
    (hI : Integrable (fun x => Φ (f x)) (torusMeasure d)) :
    Integrable (fun x => Φ (polarize i a f x)) (torusMeasure d) := by
  have hr := reflection_integrable i a hI
  apply (hI.abs.add hr.abs).mono'
    (hΦ.comp_aemeasurable (polarize_aestronglyMeasurable i a hf).aemeasurable).aestronglyMeasurable
  filter_upwards with x
  change |Φ (polarize i a f x)| ≤ |Φ (f x)|+|Φ (f (reflection i a x))|
  rcases polarize_value_or_reflected i a f x with hx | hx
  · rw [hx]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [hx]
    exact le_add_of_nonneg_left (abs_nonneg _)

/-- In particular this preserves entropy and every finite power integral. -/
theorem polarize_integral_transform {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (torusMeasure d)) {Φ : ℝ → ℝ} (hΦ : Measurable Φ)
    (hI : Integrable (fun x => Φ (f x)) (torusMeasure d)) :
    (∫ x, Φ (polarize i a f x) ∂torusMeasure d) = ∫ x, Φ (f x) ∂torusMeasure d := by
  have hp := polarize_transform_integrable i a hf hΦ hI
  have he : (∫ x, Φ (polarize i a f x)+Φ (polarize i a f (reflection i a x)) ∂torusMeasure d) =
      ∫ x, Φ (f x)+Φ (f (reflection i a x)) ∂torusMeasure d := by
    exact integral_congr_ae (Filter.Eventually.of_forall (polarize_pair i a f Φ))
  rw [integral_add hp (reflection_integrable i a hp), integral_add hI (reflection_integrable i a hI)] at he
  have hpr := reflection_integral i a (fun x => Φ (polarize i a f x))
  have hfr := reflection_integral i a (fun x => Φ (f x))
  linarith

theorem polarize_integrable {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) : Integrable (polarize i a f) (torusMeasure d) :=
  polarize_transform_integrable i a hf.aestronglyMeasurable measurable_id hf

theorem polarize_integral {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    (∫ x, polarize i a f x ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d :=
  polarize_integral_transform i a hf.aestronglyMeasurable measurable_id hf

theorem polarize_memLp_two {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) : MemLp (polarize i a f) 2 (torusMeasure d) := by
  apply (memLp_two_iff_integrable_sq (polarize_aestronglyMeasurable i a hf.aestronglyMeasurable)).mpr
  exact polarize_transform_integrable i a hf.aestronglyMeasurable (measurable_id.pow_const 2)
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf)

theorem polarize_integral_sq {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    (∫ x, (polarize i a f x)^2 ∂torusMeasure d) = ∫ x, (f x)^2 ∂torusMeasure d :=
  polarize_integral_transform i a hf.aestronglyMeasurable (measurable_id.pow_const 2)
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf)

theorem polarize_entropy_integrable {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (torusMeasure d))
    (hE : Integrable (fun x => f x*Real.log (f x)) (torusMeasure d)) :
    Integrable (fun x => polarize i a f x*Real.log (polarize i a f x)) (torusMeasure d) :=
  polarize_transform_integrable i a hf Real.continuous_mul_log.measurable hE

theorem polarize_entropy {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (torusMeasure d))
    (hE : Integrable (fun x => f x*Real.log (f x)) (torusMeasure d)) :
    densityEntropy (polarize i a f) = densityEntropy f :=
  polarize_integral_transform i a hf Real.continuous_mul_log.measurable hE


theorem polarize_L2_norm {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    ‖(polarize_memLp_two i a hf).toLp (polarize i a f)‖ = ‖hf.toLp f‖ := by
  have he := polarize_integral_sq i a hf
  rw [ExponentialPartitionContinuity.integral_sq_toLp (polarize_memLp_two i a hf),
    ExponentialPartitionContinuity.integral_sq_toLp hf] at he
  nlinarith [norm_nonneg ((polarize_memLp_two i a hf).toLp (polarize i a f)), norm_nonneg (hf.toLp f)]

/-- Equality of push-forward distributions, for every measurable subset of the real line. -/
theorem polarize_distribution {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ} (hf : Measurable f) :
    Measure.map (polarize i a f) (torusMeasure d) = Measure.map f (torusMeasure d) := by
  apply Measure.ext
  intro s hs
  have hpre := hs.preimage hf
  have hp := hs.preimage (polarize_measurable i a hf)
  have hI : Integrable (fun x => s.indicator (fun _ : ℝ => (1 : ℝ)) (f x)) (torusMeasure d) := by
    simpa only [Set.indicator, mem_preimage] using! (integrable_const (1 : ℝ)).indicator hpre
  have he := polarize_integral_transform i a hf.aestronglyMeasurable
    (measurable_const.indicator hs) hI
  have hfint : (∫ x, s.indicator (fun _ : ℝ => (1 : ℝ)) (f x) ∂torusMeasure d) =
      (torusMeasure d).real (f ⁻¹' s) := by
    convert! integral_indicator_const (1 : ℝ) hpre using 1
    simp
  have hpint : (∫ x, s.indicator (fun _ : ℝ => (1 : ℝ)) (polarize i a f x) ∂torusMeasure d) =
      (torusMeasure d).real ((polarize i a f) ⁻¹' s) := by
    convert! integral_indicator_const (1 : ℝ) hp using 1
    simp
  rw [hfint, hpint, Measure.real_def, Measure.real_def] at he
  rw [Measure.map_apply (polarize_measurable i a hf) hs, Measure.map_apply hf hs]
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp he with he | he | he
  · exact he
  · exact False.elim ((measure_ne_top _ _) he.2)
  · exact False.elim ((measure_ne_top _ _) he.1)

#print axioms polarize_distribution
#print axioms polarize_L2_norm
#print axioms polarize_integral_transform
#print axioms polarize_integral_sq
#print axioms polarize_entropy
end Legacy.BecknerOnofri.CoordinatePolarization

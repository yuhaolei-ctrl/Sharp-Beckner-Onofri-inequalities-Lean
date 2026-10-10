module

public import Legacy.TorusEndpoint.EndpointSharpnessHeat
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section

/-! # Row S006 (input to the concentration test): the Green energy of a density is the pairing of the
Green function with its autocorrelation

For a bounded measurable probability density `f` on the torus put
`φ(w) = ∫ f(w + y) f(y) dy`.  The shear `(x, y) ↦ (x - y, y)` preserves the product Haar measure, and
`f(x - y + y) = f(x)`, so
`∫∫ G(x - y) f(x) f(y) = ∫ G(w) φ(w) dw`
for the Green function `G` of the torus (`Legacy.TorusEndpoint.GreenKernelReal.realGreen`, an
`L²` class).  The function `φ` is nonnegative, bounded by `sup f`, has integral `1`, and, when `f`
vanishes outside a ball of radius `a` for the sup of the circle norms, vanishes outside the ball of
radius `2a`.  These are the properties used to localize the energy. -/

noncomputable section
open MeasureTheory Set
open Legacy.TorusEndpoint

namespace BecknerOnofri.V2.Reaudit.Obstruction

variable {d : ℕ}

instance torusMeasure_addLeftInvariant (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  rw [torusMeasure_explicit]; infer_instance

/-- The autocorrelation `w ↦ ∫ f(w + y) f(y) dy` of a function on the torus. -/
def autocorrelation (f : Torus d → ℝ) (w : Torus d) : ℝ :=
  ∫ y, f (w + y) * f y ∂torusMeasure d

section Basic

variable {f : Torus d → ℝ} {M : ℝ}

lemma measurable_autocorrelation_integrand (hm : Measurable f) :
    Measurable (fun p : Torus d × Torus d => f (p.1 + p.2) * f p.2) :=
  (hm.comp (measurable_fst.add measurable_snd)).mul (hm.comp measurable_snd)

lemma integrable_autocorrelation_integrand (hm : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hM : ∀ x, f x ≤ M) (hi : Integrable f (torusMeasure d)) :
    Integrable (fun p : Torus d × Torus d => f (p.1 + p.2) * f p.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  refine Integrable.mono' ((integrable_const M).mul_prod hi)
    (measurable_autocorrelation_integrand hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn _) (hnn _))]
  exact mul_le_mul_of_nonneg_right (hM _) (hnn _)

lemma integrable_shift_mul (hm : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hi : Integrable f (torusMeasure d)) (w : Torus d) :
    Integrable (fun y => f (w + y) * f y) (torusMeasure d) := by
  refine Integrable.mono' (hi.const_mul M)
    ((hm.comp (measurable_const.add measurable_id)).mul hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn _) (hnn _))]
  exact mul_le_mul_of_nonneg_right (hM _) (hnn _)

lemma measurable_autocorrelation (hm : Measurable f) : Measurable (autocorrelation f) :=
  (measurable_autocorrelation_integrand hm).stronglyMeasurable.integral_prod_right'.measurable

lemma autocorrelation_nonneg (hnn : ∀ x, 0 ≤ f x) (w : Torus d) : 0 ≤ autocorrelation f w :=
  integral_nonneg fun _ => mul_nonneg (hnn _) (hnn _)

lemma autocorrelation_le (hm : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hi : Integrable f (torusMeasure d)) (hmass : ∫ x, f x ∂torusMeasure d = 1) (w : Torus d) :
    autocorrelation f w ≤ M := by
  have h : autocorrelation f w ≤ ∫ y, M * f y ∂torusMeasure d := by
    apply integral_mono (integrable_shift_mul hm hnn hM hi w) (hi.const_mul M)
    intro y
    exact mul_le_mul_of_nonneg_right (hM _) (hnn _)
  rwa [integral_const_mul, hmass, mul_one] at h

lemma integral_autocorrelation (hm : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hi : Integrable f (torusMeasure d)) (hmass : ∫ x, f x ∂torusMeasure d = 1) :
    ∫ w, autocorrelation f w ∂torusMeasure d = 1 := by
  unfold autocorrelation
  rw [integral_integral_swap (integrable_autocorrelation_integrand hm hnn hM hi)]
  have h : ∀ y, ∫ w, f (w + y) * f y ∂torusMeasure d = f y := fun y => by
    rw [integral_mul_const, integral_add_right_eq_self (fun w => f w) y, hmass, one_mul]
  simp_rw [h]
  exact hmass

lemma autocorrelation_support {a : ℝ} (hsupp : ∀ x, f x ≠ 0 → ∀ j, ‖x j‖ ≤ a) {w : Torus d}
    (hw : autocorrelation f w ≠ 0) : ∀ j, ‖w j‖ ≤ 2 * a := by
  intro j
  by_contra hcon
  apply hw
  have h0 : ∀ y, f (w + y) * f y = 0 := by
    intro y
    by_contra hy
    have a1 := hsupp _ (left_ne_zero_of_mul hy) j
    have a2 := hsupp _ (right_ne_zero_of_mul hy) j
    have h3 : ‖w j‖ ≤ ‖(w + y) j‖ + ‖y j‖ := by
      calc ‖w j‖ = ‖(w + y) j - y j‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    linarith
  unfold autocorrelation
  simp [h0]

end Basic

/-- The shear `(x, y) ↦ (x - y, y)` of the torus squared, as a measurable equivalence. -/
def shearSub (d : ℕ) : Torus d × Torus d ≃ᵐ Torus d × Torus d where
  toFun p := (p.1 - p.2, p.2)
  invFun q := (q.1 + q.2, q.2)
  left_inv p := by simp
  right_inv q := by simp
  measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd

lemma shearSub_measurePreserving (d : ℕ) :
    MeasurePreserving (shearSub d) ((torusMeasure d).prod (torusMeasure d))
      ((torusMeasure d).prod (torusMeasure d)) :=
  measurePreserving_sub_prod (torusMeasure d) (torusMeasure d)

/-- **The Green energy of a bounded density is the pairing of the Green function with the
autocorrelation of the density.** -/
theorem physicalGreenEnergy_eq_integral_autocorrelation (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    PhysicalGreenL2.physicalGreenEnergy r =
      ∫ w, GreenKernelReal.realGreen d w * autocorrelation r.value w ∂torusMeasure d := by
  have hI := PhysicalGreenL2.realGreen_interaction_integrable r hr
  have hmp := shearSub_measurePreserving d
  set F : Torus d × Torus d → ℝ :=
    fun q => GreenKernelReal.realGreen d q.1 * r.value (q.1 + q.2) * r.value q.2 with hF
  have hFe : ∀ p : Torus d × Torus d, F (shearSub d p) =
      GreenKernelReal.realGreen d (p.1 - p.2) * r.value p.1 * r.value p.2 := by
    intro p
    simp [hF, shearSub]
  have hFi : Integrable F ((torusMeasure d).prod (torusMeasure d)) := by
    rw [← hmp.integrable_comp_emb (shearSub d).measurableEmbedding]
    have : (F ∘ shearSub d) = fun p : Torus d × Torus d =>
        GreenKernelReal.realGreen d (p.1 - p.2) * r.value p.1 * r.value p.2 := funext hFe
    rw [this]
    exact hI
  unfold PhysicalGreenL2.physicalGreenEnergy
  rw [← integral_prod _ hI]
  have h2 : (∫ p, GreenKernelReal.realGreen d (p.1 - p.2) * r.value p.1 * r.value p.2
      ∂(torusMeasure d).prod (torusMeasure d)) = ∫ q, F q ∂(torusMeasure d).prod (torusMeasure d) := by
    rw [← hmp.integral_comp' F]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => (hFe p).symm)
  rw [h2, integral_prod _ hFi]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun w => ?_
  simp only [hF, autocorrelation]
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  simp only [mul_assoc]

end BecknerOnofri.V2.Reaudit.Obstruction

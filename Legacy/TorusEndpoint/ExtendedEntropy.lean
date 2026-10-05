import Legacy.TorusEndpoint.TorusFourier
import Legacy.TorusEndpoint.EntropyVariational
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Extended entropy for every probability density

The entropy is defined by the nonnegative shifted integrand r*log r-r+1.
Its Lebesgue integral is meaningful before any entropy integrability is
assumed. Probability normalization removes the shift in the finite case.
The negative part of r*log r is bounded and integrable for every density.
No extended physical interaction energy is defined or postulated here.
-/

open MeasureTheory
open scoped ENNReal

namespace Legacy.TorusEndpoint

/-- The nonnegative relative-entropy integrand on nonnegative real inputs. -/
noncomputable def entropyShift (r : ℝ) : ℝ := r * Real.log r - r + 1

theorem entropyShift_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ entropyShift r := by
  simpa [entropyShift] using entropy_young r 0 hr

theorem entropy_integrand_lower_bound {r : ℝ} (hr : 0 ≤ r) :
    -1 ≤ r * Real.log r := by
  have h := entropyShift_nonneg hr
  dsimp [entropyShift] at h
  linarith

/-- The extended entropy is defined for every actual probability density,
including those for which the real entropy integrand is not integrable. -/
noncomputable def extendedDensityEntropy {d : ℕ} (rho : ProbabilityDensity d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (entropyShift (rho.value x)) ∂torusMeasure d

theorem density_entropy_integrand_aestronglyMeasurable {d : ℕ}
    (rho : ProbabilityDensity d) :
    AEStronglyMeasurable (fun x => rho.value x * Real.log (rho.value x))
      (torusMeasure d) := by
  have h := rho.integrable.aestronglyMeasurable.aemeasurable
  exact (h.mul (Real.measurable_log.comp_aemeasurable h)).aestronglyMeasurable

theorem density_entropyShift_aestronglyMeasurable {d : ℕ}
    (rho : ProbabilityDensity d) :
    AEStronglyMeasurable (fun x => entropyShift (rho.value x)) (torusMeasure d) := by
  exact ((density_entropy_integrand_aestronglyMeasurable rho).sub
    rho.integrable.aestronglyMeasurable).add aestronglyMeasurable_const

theorem density_entropyShift_nonneg_ae {d : ℕ} (rho : ProbabilityDensity d) :
    ∀ᵐ x ∂torusMeasure d, 0 ≤ entropyShift (rho.value x) := by
  filter_upwards [rho.nonneg] with x hx
  exact entropyShift_nonneg hx

/-- The usual negative part of rho*log rho is uniformly bounded by one. -/
theorem density_entropy_neg_part_le_one {d : ℕ} (rho : ProbabilityDensity d) :
    ∀ᵐ x ∂torusMeasure d,
      max (-(rho.value x * Real.log (rho.value x))) 0 ≤ 1 := by
  filter_upwards [rho.nonneg] with x hx
  exact max_le (by linarith [entropy_integrand_lower_bound hx]) (by norm_num)

theorem density_entropy_neg_part_integrable {d : ℕ} (rho : ProbabilityDensity d) :
    Integrable (fun x => max (-(rho.value x * Real.log (rho.value x))) 0)
      (torusMeasure d) := by
  have hm : AEStronglyMeasurable
      (fun x => max (-(rho.value x * Real.log (rho.value x))) 0) (torusMeasure d) :=
    ((density_entropy_integrand_aestronglyMeasurable rho).aemeasurable.neg.max
      aemeasurable_const).aestronglyMeasurable
  apply (integrable_const (1 : ℝ)).mono' hm
  filter_upwards [density_entropy_neg_part_le_one rho] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact hx

theorem density_entropy_neg_lintegral_le_one {d : ℕ} (rho : ProbabilityDensity d) :
    (∫⁻ x, ENNReal.ofReal (-(rho.value x * Real.log (rho.value x)))
      ∂torusMeasure d) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _x : Torus d, (1 : ℝ≥0∞) ∂torusMeasure d := by
      apply lintegral_mono_ae
      filter_upwards [rho.nonneg] with x hx
      have h : -(rho.value x * Real.log (rho.value x)) ≤ 1 := by
        linarith [entropy_integrand_lower_bound hx]
      simpa using ENNReal.ofReal_le_ofReal h
    _ = 1 := by simp

/-- Adding the integrable affine correction does not change the finite
entropy condition. Both directions are proved before using Bochner integrals. -/
theorem integrable_entropyShift_iff {d : ℕ} (rho : ProbabilityDensity d) :
    Integrable (fun x => entropyShift (rho.value x)) (torusMeasure d) ↔
      rho.FiniteEntropy := by
  constructor
  · intro h
    have heq : (fun x => rho.value x * Real.log (rho.value x)) =
        (fun x => entropyShift (rho.value x)) + rho.value - (fun _ => (1 : ℝ)) := by
      funext x
      dsimp [entropyShift]
      ring
    change Integrable (fun x => rho.value x * Real.log (rho.value x)) (torusMeasure d)
    rw [heq]
    exact (h.add rho.integrable).sub (integrable_const 1)
  · intro h
    change Integrable (fun x => rho.value x * Real.log (rho.value x)) (torusMeasure d) at h
    exact (h.sub rho.integrable).add (integrable_const 1)

/-- Finiteness of the extended entropy is exactly the earlier explicit
integrability predicate, not an additional assumption in its definition. -/
theorem finiteEntropy_iff_extendedDensityEntropy_ne_top {d : ℕ}
    (rho : ProbabilityDensity d) :
    rho.FiniteEntropy ↔ extendedDensityEntropy rho ≠ ∞ := by
  rw [← integrable_entropyShift_iff rho]
  exact (lintegral_ofReal_ne_top_iff_integrable
    (density_entropyShift_aestronglyMeasurable rho) (density_entropyShift_nonneg_ae rho)).symm

theorem finiteEntropy_iff_extendedDensityEntropy_lt_top {d : ℕ}
    (rho : ProbabilityDensity d) :
    rho.FiniteEntropy ↔ extendedDensityEntropy rho < ∞ := by
  rw [lt_top_iff_ne_top]
  exact finiteEntropy_iff_extendedDensityEntropy_ne_top rho

theorem extendedDensityEntropy_eq_top_of_not_finite {d : ℕ}
    (rho : ProbabilityDensity d) (h : ¬ rho.FiniteEntropy) :
    extendedDensityEntropy rho = ∞ := by
  by_contra hn
  exact h ((finiteEntropy_iff_extendedDensityEntropy_ne_top rho).mpr hn)

theorem integral_entropyShift_eq_densityEntropy {d : ℕ}
    (rho : ProbabilityDensity d) (h : rho.FiniteEntropy) :
    (∫ x, entropyShift (rho.value x) ∂torusMeasure d) = densityEntropy rho.value := by
  change Integrable (fun x => rho.value x * Real.log (rho.value x)) (torusMeasure d) at h
  change (∫ x, (((fun x : Torus d => rho.value x * Real.log (rho.value x)) - rho.value) +
      (fun _ : Torus d => (1 : ℝ))) x ∂torusMeasure d) = _
  rw [integral_add' (h.sub rho.integrable) (integrable_const 1),
    integral_sub' h rho.integrable, rho.mass]
  unfold densityEntropy
  simp

theorem densityEntropy_nonneg_of_finite {d : ℕ}
    (rho : ProbabilityDensity d) (h : rho.FiniteEntropy) :
    0 ≤ densityEntropy rho.value := by
  rw [← integral_entropyShift_eq_densityEntropy rho h]
  exact integral_nonneg_of_ae (density_entropyShift_nonneg_ae rho)

theorem extendedDensityEntropy_eq_ofReal_of_finite {d : ℕ}
    (rho : ProbabilityDensity d) (h : rho.FiniteEntropy) :
    extendedDensityEntropy rho = ENNReal.ofReal (densityEntropy rho.value) := by
  rw [extendedDensityEntropy, ← ofReal_integral_eq_lintegral_ofReal
    ((integrable_entropyShift_iff rho).mpr h) (density_entropyShift_nonneg_ae rho),
    integral_entropyShift_eq_densityEntropy rho h]

/-- The negative-part Lebesgue integral is always finite, independently of
the finiteness of entropy. In particular no infinity-minus-infinity occurs. -/
theorem density_entropy_neg_lintegral_ne_top {d : ℕ} (rho : ProbabilityDensity d) :
    (∫⁻ x, ENNReal.ofReal (-(rho.value x * Real.log (rho.value x)))
      ∂torusMeasure d) ≠ ∞ :=
  ne_top_of_le_ne_top (by norm_num) (density_entropy_neg_lintegral_le_one rho)

theorem density_entropy_pos_part_integrable_iff {d : ℕ} (rho : ProbabilityDensity d) :
    Integrable (fun x => max (rho.value x * Real.log (rho.value x)) 0)
      (torusMeasure d) ↔ rho.FiniteEntropy := by
  constructor
  · intro h
    have hd := h.sub (density_entropy_neg_part_integrable rho)
    change Integrable (fun x => rho.value x * Real.log (rho.value x)) (torusMeasure d)
    have heq : (fun x => rho.value x * Real.log (rho.value x)) =
        (fun x => max (rho.value x * Real.log (rho.value x)) 0) -
          (fun x => max (-(rho.value x * Real.log (rho.value x))) 0) := by
      funext x
      exact (max_zero_sub_max_neg_zero_eq_self _).symm
    rw [heq]
    exact hd
  · intro h
    exact h.pos_part

theorem density_entropy_pos_lintegral_eq_top_of_not_finite {d : ℕ}
    (rho : ProbabilityDensity d) (h : ¬ rho.FiniteEntropy) :
    (∫⁻ x, ENNReal.ofReal (rho.value x * Real.log (rho.value x))
      ∂torusMeasure d) = ∞ := by
  by_contra hn
  have hm : AEStronglyMeasurable
      (fun x => max (rho.value x * Real.log (rho.value x)) 0) (torusMeasure d) :=
    ((density_entropy_integrand_aestronglyMeasurable rho).aemeasurable.max
      aemeasurable_const).aestronglyMeasurable
  have hp : ∀ᵐ x ∂torusMeasure d,
      0 ≤ max (rho.value x * Real.log (rho.value x)) 0 :=
    Filter.Eventually.of_forall (fun x => le_max_right _ _)
  have hi : Integrable (fun x => max (rho.value x * Real.log (rho.value x)) 0)
      (torusMeasure d) :=
    (lintegral_ofReal_ne_top_iff_integrable hm hp).mp (by simpa using hn)
  exact h ((density_entropy_pos_part_integrable_iff rho).mp hi)

/-- The nonnegative shifted definition agrees, on its entire domain, with
the usual extended signed entropy integral. The subtracted negative-part
integral is proved finite above, including when the positive part is infinite. -/
theorem extendedDensityEntropy_eq_pos_sub_neg {d : ℕ} (rho : ProbabilityDensity d) :
    extendedDensityEntropy rho =
      (∫⁻ x, ENNReal.ofReal (rho.value x * Real.log (rho.value x)) ∂torusMeasure d) -
      (∫⁻ x, ENNReal.ofReal (-(rho.value x * Real.log (rho.value x))) ∂torusMeasure d) := by
  by_cases h : rho.FiniteEntropy
  · have hp := (density_entropy_pos_part_integrable_iff rho).mpr h
    have hn := density_entropy_neg_part_integrable rho
    have hp_eq : ENNReal.ofReal
        (∫ x, max (rho.value x * Real.log (rho.value x)) 0 ∂torusMeasure d) =
        ∫⁻ x, ENNReal.ofReal (rho.value x * Real.log (rho.value x)) ∂torusMeasure d := by
      simpa using ofReal_integral_eq_lintegral_ofReal hp
        (Filter.Eventually.of_forall (fun x => le_max_right _ _))
    have hn_eq : ENNReal.ofReal
        (∫ x, max (-(rho.value x * Real.log (rho.value x))) 0 ∂torusMeasure d) =
        ∫⁻ x, ENNReal.ofReal (-(rho.value x * Real.log (rho.value x))) ∂torusMeasure d := by
      simpa using ofReal_integral_eq_lintegral_ofReal hn
        (Filter.Eventually.of_forall (fun x => le_max_right _ _))
    have hdiff :
        (∫ x, max (rho.value x * Real.log (rho.value x)) 0 ∂torusMeasure d) -
        (∫ x, max (-(rho.value x * Real.log (rho.value x))) 0 ∂torusMeasure d) =
        densityEntropy rho.value := by
      rw [← integral_sub hp hn]
      unfold densityEntropy
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => max_zero_sub_max_neg_zero_eq_self _)
    have hn0 : 0 ≤ (∫ x, max (-(rho.value x * Real.log (rho.value x))) 0
        ∂torusMeasure d) := integral_nonneg (fun x => le_max_right _ _)
    rw [extendedDensityEntropy_eq_ofReal_of_finite rho h, ← hdiff,
      ENNReal.ofReal_sub _ hn0, hp_eq, hn_eq]
  · rw [extendedDensityEntropy_eq_top_of_not_finite rho h,
      density_entropy_pos_lintegral_eq_top_of_not_finite rho h,
      ENNReal.top_sub (density_entropy_neg_lintegral_ne_top rho)]

/-- In the genuinely infinite-entropy case every extended nonnegative
quantity is below the entropy. This is an order fact, not a kernel assertion. -/
theorem le_extendedDensityEntropy_of_not_finite {d : ℕ}
    (rho : ProbabilityDensity d) (h : ¬ rho.FiniteEntropy) (E : ℝ≥0∞) :
    E ≤ extendedDensityEntropy rho := by
  rw [extendedDensityEntropy_eq_top_of_not_finite rho h]
  exact le_top

/-- A finite-entropy comparison in the extended order suffices for all
densities, with the infinite case now handled by the proved definition. -/
theorem extendedDensityEntropy_bound_of_finite_cases {d : ℕ}
    (E : ProbabilityDensity d → ℝ≥0∞)
    (hfinite : ∀ rho : ProbabilityDensity d, rho.FiniteEntropy →
      E rho ≤ ENNReal.ofReal (densityEntropy rho.value))
    (rho : ProbabilityDensity d) : E rho ≤ extendedDensityEntropy rho := by
  by_cases h : rho.FiniteEntropy
  · rw [extendedDensityEntropy_eq_ofReal_of_finite rho h]
    exact hfinite rho h
  · exact le_extendedDensityEntropy_of_not_finite rho h (E rho)

end Legacy.TorusEndpoint

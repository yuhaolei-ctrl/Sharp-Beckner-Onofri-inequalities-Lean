import Legacy.BecknerOnofri.PolarizationPairing

/-! Integrating the genuine four-point comparison over the actual Haar product measure. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.CoordinatePolarization

def pairingIntegrand {d : ℕ} (K : Torus d → Torus d → ℝ) (f : Torus d → ℝ)
    (p : Torus d × Torus d) : ℝ := K p.1 p.2*f p.1*f p.2

def pairing {d : ℕ} (K : Torus d → Torus d → ℝ) (f : Torus d → ℝ) : ℝ :=
  ∫ p, pairingIntegrand K f p ∂(torusMeasure d).prod (torusMeasure d)

theorem reflected_pairing_integrable {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (f : Torus d → ℝ) (hI : Integrable (pairingIntegrand K f) ((torusMeasure d).prod (torusMeasure d))) :
    Integrable (fun p : Torus d × Torus d => fourPoint i a K f p.1 p.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  have hleft := ((reflection_measurePreserving i a).prod (MeasurePreserving.id (torusMeasure d))).integrable_comp hI.aestronglyMeasurable |>.mpr hI
  have hright := ((MeasurePreserving.id (torusMeasure d)).prod (reflection_measurePreserving i a)).integrable_comp hI.aestronglyMeasurable |>.mpr hI
  have hboth := ((reflection_measurePreserving i a).prod (reflection_measurePreserving i a)).integrable_comp hI.aestronglyMeasurable |>.mpr hI
  exact ((hI.add hright).add hleft).add hboth

theorem fourPoint_integral {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (f : Torus d → ℝ) (hI : Integrable (pairingIntegrand K f) ((torusMeasure d).prod (torusMeasure d))) :
    (∫ p : Torus d × Torus d, fourPoint i a K f p.1 p.2 ∂(torusMeasure d).prod (torusMeasure d)) = 4*pairing K f := by
  let μ := torusMeasure d
  have hmpL := (reflection_measurePreserving i a).prod (MeasurePreserving.id μ)
  have hmpR := (MeasurePreserving.id μ).prod (reflection_measurePreserving i a)
  have hmpB := (reflection_measurePreserving i a).prod (reflection_measurePreserving i a)
  have hL := (hmpL.integrable_comp hI.aestronglyMeasurable).mpr hI
  have hR := (hmpR.integrable_comp hI.aestronglyMeasurable).mpr hI
  have hB := (hmpB.integrable_comp hI.aestronglyMeasurable).mpr hI
  have heL := hmpL.integral_comp ((reflectionEquiv i a).prodCongr (MeasurableEquiv.refl (Torus d))).measurableEmbedding (pairingIntegrand K f)
  have heR := hmpR.integral_comp ((MeasurableEquiv.refl (Torus d)).prodCongr (reflectionEquiv i a)).measurableEmbedding (pairingIntegrand K f)
  have heB := hmpB.integral_comp ((reflectionEquiv i a).prodCongr (reflectionEquiv i a)).measurableEmbedding (pairingIntegrand K f)
  change (∫ p, (pairingIntegrand K f + (pairingIntegrand K f ∘ Prod.map id (reflection i a)) +
      (pairingIntegrand K f ∘ Prod.map (reflection i a) id) +
      (pairingIntegrand K f ∘ Prod.map (reflection i a) (reflection i a))) p ∂μ.prod μ) = _
  rw [integral_add' ((hI.add hR).add hL) hB, integral_add' (hI.add hR) hL, integral_add' hI hR]
  change (∫ p, pairingIntegrand K f p ∂μ.prod μ) + _ + _ + _ = _
  unfold pairing
  dsimp [μ] at heL heR heB ⊢
  linarith

/-- The only geometric hypotheses are reflection symmetry and the same-side kernel comparison. -/
theorem pairing_polarize_le_of_integrable {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (hmono : ∀ x ∈ halfTorus i a, ∀ y ∈ halfTorus i a, K x (reflection i a y) ≤ K x y)
    (f : Torus d → ℝ)
    (hI : Integrable (pairingIntegrand K f) ((torusMeasure d).prod (torusMeasure d)))
    (hP : Integrable (pairingIntegrand K (polarize i a f)) ((torusMeasure d).prod (torusMeasure d))) :
    pairing K f ≤ pairing K (polarize i a f) := by
  have h := integral_mono_ae (reflected_pairing_integrable i a K f hI)
    (reflected_pairing_integrable i a K (polarize i a f) hP)
    (Filter.Eventually.of_forall (fun p => fourPoint_polarize_le i a K hK hmono f p.1 p.2))
  rw [fourPoint_integral i a K f hI, fourPoint_integral i a K (polarize i a f) hP] at h
  linarith

theorem pairingIntegrand_integrable_bounded {d : ℕ} (K : Torus d → Torus d → ℝ)
    (hK : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y, ‖K x y‖ ≤ C)
    {f : Torus d → ℝ} (hf : Integrable f (torusMeasure d)) :
    Integrable (pairingIntegrand K f) ((torusMeasure d).prod (torusMeasure d)) := by
  have h := (hf.mul_prod hf).bdd_mul hK.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hC p.1 p.2))
  change Integrable (fun p : Torus d × Torus d => K p.1 p.2*f p.1*f p.2) _
  simpa only [Function.uncurry_def, mul_assoc] using! h

/-- For bounded measurable kernels and actual L¹ functions, all product-integrability obligations are discharged. -/
theorem pairing_polarize_le_bounded {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y, ‖K x y‖ ≤ C)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (hmono : ∀ x ∈ halfTorus i a, ∀ y ∈ halfTorus i a, K x (reflection i a y) ≤ K x y)
    {f : Torus d → ℝ} (hf : Integrable f (torusMeasure d)) :
    pairing K f ≤ pairing K (polarize i a f) :=
  pairing_polarize_le_of_integrable i a K hK hmono f
    (pairingIntegrand_integrable_bounded K hmeas hC hf)
    (pairingIntegrand_integrable_bounded K hmeas hC (polarize_integrable i a hf))

#print axioms pairing_polarize_le_of_integrable
#print axioms pairing_polarize_le_bounded
end Legacy.BecknerOnofri.CoordinatePolarization

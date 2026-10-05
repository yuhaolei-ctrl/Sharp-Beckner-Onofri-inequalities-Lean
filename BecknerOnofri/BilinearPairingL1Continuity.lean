module

public import BecknerOnofri.BilinearPolarizationIntegral

@[expose] public section

/-! The quantitative L1 continuity needed to pass a bounded-kernel
rearrangement inequality from regular functions to the full L1 domain. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace BecknerOnofri.BilinearPolarization

lemma pairing_norm_le {d : ℕ} (K : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (f g : Torus d → ℝ) (hf : Integrable f (torusMeasure d))
    (hg : Integrable g (torusMeasure d)) :
    ‖pairing K f g‖≤C*(∫ x,‖f x‖ ∂torusMeasure d)*(∫ x,‖g x‖ ∂torusMeasure d) := by
  have hI := pairingIntegrand_integrable_bounded K hmeas hC hf hg
  calc
    _ ≤ ∫ p,‖pairingIntegrand K f g p‖ ∂(torusMeasure d).prod (torusMeasure d) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p : Torus d × Torus d,C*(‖f p.1‖*‖g p.2‖)
        ∂(torusMeasure d).prod (torusMeasure d) := by
      apply integral_mono hI.norm ((hf.norm.mul_prod hg.norm).const_mul C)
      intro p
      simp only [pairingIntegrand,norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC p.1 p.2) (norm_nonneg _)) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _)
    _ = _ := by rw [integral_const_mul,
      integral_prod_mul (fun x => ‖f x‖) (fun x => ‖g x‖)]; ring

lemma pairing_sub_left {d : ℕ} (K : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (f f' g : Torus d → ℝ) (hf : Integrable f (torusMeasure d))
    (hf' : Integrable f' (torusMeasure d)) (hg : Integrable g (torusMeasure d)) :
    pairing K (f-f') g=pairing K f g-pairing K f' g := by
  have he : pairingIntegrand K (f-f') g=pairingIntegrand K f g-pairingIntegrand K f' g := by
    funext p; simp only [pairingIntegrand,Pi.sub_apply]; ring
  unfold pairing
  rw [he,integral_sub' (pairingIntegrand_integrable_bounded K hmeas hC hf hg)
    (pairingIntegrand_integrable_bounded K hmeas hC hf' hg)]

lemma pairing_sub_right {d : ℕ} (K : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (f g g' : Torus d → ℝ) (hf : Integrable f (torusMeasure d))
    (hg : Integrable g (torusMeasure d)) (hg' : Integrable g' (torusMeasure d)) :
    pairing K f (g-g')=pairing K f g-pairing K f g' := by
  have he : pairingIntegrand K f (g-g')=pairingIntegrand K f g-pairingIntegrand K f g' := by
    funext p; simp only [pairingIntegrand,Pi.sub_apply]; ring
  unfold pairing
  rw [he,integral_sub' (pairingIntegrand_integrable_bounded K hmeas hC hf hg)
    (pairingIntegrand_integrable_bounded K hmeas hC hf hg')]

/-- The exact bilinear error bound, with no uniform bound on the functions. -/
theorem pairing_l1_error {d : ℕ} (K : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (f f' g g' : Torus d → ℝ) (hf : Integrable f (torusMeasure d))
    (hf' : Integrable f' (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    (hg' : Integrable g' (torusMeasure d)) :
    ‖pairing K f g-pairing K f' g'‖≤
      C*(∫ x,‖f x-f' x‖ ∂torusMeasure d)*(∫ x,‖g x‖ ∂torusMeasure d)+
      C*(∫ x,‖f' x‖ ∂torusMeasure d)*(∫ x,‖g x-g' x‖ ∂torusMeasure d) := by
  have he : pairing K f g-pairing K f' g'=
      pairing K (f-f') g+pairing K f' (g-g') := by
    rw [pairing_sub_left K hmeas hC f f' g hf hf' hg,
      pairing_sub_right K hmeas hC f' g g' hf' hg hg']; ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (pairing_norm_le K hmeas hC (f-f') g (hf.sub hf') hg)
    (pairing_norm_le K hmeas hC f' (g-g') hf' (hg.sub hg')))

#print axioms pairing_l1_error
end BecknerOnofri.BilinearPolarization

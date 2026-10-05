module

public import BecknerOnofri.PolarizationL1Contraction

@[expose] public section

noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization
attribute [local instance] Classical.propDecidable

/-- Pointwise order is preserved by genuine simultaneous max/min sorting. -/
theorem polarize_mono {d : ℕ} (i : Fin d) (a : ℝ) {f g : Torus d → ℝ}
    (h : ∀ x,f x≤g x) : ∀ x,polarize i a f x≤polarize i a g x := by
  intro x
  unfold polarize
  split_ifs
  · exact max_le_max (h x) (h _)
  · exact min_le_min (h x) (h _)

theorem polarize_mono_ae {d : ℕ} (i : Fin d) (a : ℝ) {f g : Torus d → ℝ}
    (h : f≤ᵐ[torusMeasure d] g) : polarize i a f≤ᵐ[torusMeasure d] polarize i a g := by
  filter_upwards [h,(reflection_measurePreserving i a).quasiMeasurePreserving.ae h] with x hx hr
  unfold polarize
  split_ifs
  · exact max_le_max hx hr
  · exact min_le_min hx hr

lemma pair_distance_le_on_half {d : ℕ} (i : Fin d) (a : ℝ) (f g : Torus d → ℝ)
    {x : Torus d} (hx : x∈halfTorus i a) :
    |polarize i a f x-polarize i a g x|+
      |polarize i a f (reflection i a x)-polarize i a g (reflection i a x)|≤
      |f x-g x|+|f (reflection i a x)-g (reflection i a x)| := by
  rw [polarize_reflected_of_mem i a f hx,polarize_reflected_of_mem i a g hx]
  simp only [polarize,if_pos hx]
  exact sorted_distance_le _ _ _ _

lemma pair_distance_le {d : ℕ} (i : Fin d) (a : ℝ) (f g : Torus d → ℝ)
    (x : Torus d) :
    |polarize i a f x-polarize i a g x|+
      |polarize i a f (reflection i a x)-polarize i a g (reflection i a x)|≤
      |f x-g x|+|f (reflection i a x)-g (reflection i a x)| := by
  rcases reflection_half_or_fixed i a x with hf | hr
  · simp only [hf,polarize_of_fixed i a f hf,polarize_of_fixed i a g hf,le_refl]
  · by_cases hx : x∈halfTorus i a
    · exact pair_distance_le_on_half i a f g hx
    · have h := pair_distance_le_on_half i a f g (hr.mpr hx)
      rw [reflection_involutive i a x] at h
      simpa only [add_comm] using h

/-- L1 contraction requires only integrability; neither boundedness nor
nonnegativity is assumed. -/
theorem polarize_l1_contraction {d : ℕ} (i : Fin d) (a : ℝ) (f g : Torus d → ℝ)
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d)) :
    (∫ x,|polarize i a f x-polarize i a g x| ∂torusMeasure d)≤
      ∫ x,|f x-g x| ∂torusMeasure d := by
  have hI := (hf.sub hg).abs
  have hP := ((polarize_integrable i a hf).sub (polarize_integrable i a hg)).abs
  have h := integral_mono (hP.add (reflection_integrable i a hP))
    (hI.add (reflection_integrable i a hI)) (pair_distance_le i a f g)
  rw [integral_add' hP (reflection_integrable i a hP),
      integral_add' hI (reflection_integrable i a hI),
      reflection_integral i a (fun x => |(polarize i a f-polarize i a g) x|),
      reflection_integral i a (fun x => |(f-g) x|)] at h
  dsimp only [Pi.sub_apply] at h
  linarith

#print axioms polarize_mono
#print axioms polarize_mono_ae
#print axioms polarize_l1_contraction
end BecknerOnofri.PolarizationL1

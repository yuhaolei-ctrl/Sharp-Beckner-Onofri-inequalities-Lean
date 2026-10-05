module

public import Legacy.BecknerOnofri.CosineMomentWeight

@[expose] public section

/-! Passing almost-everywhere polarization fixed points to actual pointwise
reflection inequalities for continuous functions, including null boundary faces. -/
noncomputable section
namespace Legacy.BecknerOnofri.CoordinatePolarization
open MeasureTheory Set Legacy.TorusEndpoint
attribute [local instance] Classical.propDecidable

theorem polarize_congr_ae {d : ℕ} (i : Fin d) (a : ℝ) {f g : Torus d → ℝ}
    (h : f =ᵐ[torusMeasure d] g) : polarize i a f =ᵐ[torusMeasure d] polarize i a g := by
  have hr := (reflection_measurePreserving i a).quasiMeasurePreserving.ae_eq h
  filter_upwards [h, hr] with x hx hy
  change f (reflection i a x) = g (reflection i a x) at hy
  simp only [polarize, hx, hy]

theorem weight_order_on_complement {d : ℕ} (i : Fin d) (a : ℝ) (w : Torus d → ℝ)
    (hw : ∀ x ∈ halfTorus i a, w (reflection i a x) ≤ w x)
    {x : Torus d} (hx : x ∉ halfTorus i a) : w x ≤ w (reflection i a x) := by
  rcases reflection_half_or_fixed i a x with hfix | hside
  · rw [hfix]
  · have h := hw _ (hside.mpr hx)
    rwa [reflection_involutive i a x] at h

theorem continuous_fixed_reflection_ge {d : ℕ} (i : Fin d) (a : ℝ)
    {f w : Torus d → ℝ} (hf : Continuous f) (hw : Continuous w)
    (hmono : ∀ x ∈ halfTorus i a, w (reflection i a x) ≤ w x)
    (hfixed : polarize i a f =ᵐ[torusMeasure d] f)
    {x : Torus d} (hx : w (reflection i a x) < w x) :
    f (reflection i a x) ≤ f x := by
  let g : Torus d → ℝ := fun y =>
    max (w y-w (reflection i a y)) 0 * max (f (reflection i a y)-f y) 0
  have hg : Continuous g := by
    exact ((hw.sub (hw.comp (reflection_continuous i a))).max continuous_const).mul
      (((hf.comp (reflection_continuous i a)).sub hf).max continuous_const)
  have hg0 : g =ᵐ[torusMeasure d] (fun _ => 0) := by
    filter_upwards [hfixed] with y hy
    by_cases hs : y ∈ halfTorus i a
    · have hle : f (reflection i a y) ≤ f y := by
        have he : max (f y) (f (reflection i a y)) = f y := by simpa [polarize, hs] using hy
        exact he ▸ le_max_right (f y) (f (reflection i a y))
      simp [g, max_eq_right (sub_nonpos.mpr hle)]
    · have hle := weight_order_on_complement i a w hmono hs
      simp [g, max_eq_right (sub_nonpos.mpr hle)]
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    rw [torusMeasure_explicit]
    infer_instance
  have he := congrFun (Measure.eq_of_ae_eq hg0 hg continuous_const) x
  change max (w x-w (reflection i a x)) 0 * max (f (reflection i a x)-f x) 0 = 0 at he
  have hp : max (w x-w (reflection i a x)) 0 ≠ 0 :=
    (lt_of_lt_of_le (sub_pos.mpr hx) (le_max_left _ _)).ne'
  have hz := (mul_eq_zero.mp he).resolve_left hp
  exact sub_nonpos.mp ((le_max_left _ _).trans hz.le)

def OriginPolarizationInvariant {d : ℕ} (f : Torus d → ℝ) : Prop :=
  ∀ (i : Fin d) (a : ℝ), -(1/2:ℝ) < a → a < 0 → polarize i a f =ᵐ[torusMeasure d] f

theorem origin_fixed_reflection_ge {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (i : Fin d) {a : ℝ}
    (ha : -(1/2:ℝ) < a) (ha0 : a < 0) {x : Torus d} (hx : x ∈ halfTorus i a) :
    f (reflection i a x) ≤ f x := by
  by_cases hfix : reflection i a x = x
  · rw [hfix]
  · apply continuous_fixed_reflection_ge i a hf (CosineMomentWeight.weight_continuous d)
      (fun y hy => ?_) (hfixed i a ha ha0) (CosineMomentWeight.weight_strict i ha ha0 x hx hfix)
    by_cases hyfix : reflection i a y = y
    · rw [hyfix]
    · exact (CosineMomentWeight.weight_strict i ha ha0 y hy hyfix).le

#print axioms continuous_fixed_reflection_ge
#print axioms origin_fixed_reflection_ge
end Legacy.BecknerOnofri.CoordinatePolarization

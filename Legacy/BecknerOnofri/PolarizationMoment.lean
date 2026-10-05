import Legacy.BecknerOnofri.PolarizationPairing

/-! A monotone reflection weight gives an increasing polarization moment;
strict weights make equality force an actual polarization fixed point. -/
noncomputable section
namespace Legacy.BecknerOnofri.CoordinatePolarization
open MeasureTheory Set Legacy.TorusEndpoint
attribute [local instance] Classical.propDecidable

def pairMoment {d : ℕ} (i : Fin d) (a : ℝ) (f w : Torus d → ℝ) (x : Torus d) : ℝ :=
  f x*w x+f (reflection i a x)*w (reflection i a x)

theorem pairMoment_reflect {d : ℕ} (i : Fin d) (a : ℝ) (f w : Torus d → ℝ) (x : Torus d) :
    pairMoment i a f w (reflection i a x) = pairMoment i a f w x := by
  unfold pairMoment
  rw [reflection_involutive i a x]
  ring

theorem pairMoment_polarize_le_on_half {d : ℕ} (i : Fin d) (a : ℝ) (f w : Torus d → ℝ)
    {x : Torus d} (hx : x ∈ halfTorus i a) (hw : w (reflection i a x) ≤ w x) :
    pairMoment i a f w x ≤ pairMoment i a (polarize i a f) w x := by
  unfold pairMoment
  rw [polarize_reflected_of_mem i a f hx]
  simp only [polarize, if_pos hx]
  rcases le_total (f x) (f (reflection i a x)) with h | h
  · simp only [max_eq_right h, min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hw)]
  · simp [h]

theorem pairMoment_polarize_le {d : ℕ} (i : Fin d) (a : ℝ) (f w : Torus d → ℝ)
    (hw : ∀ x ∈ halfTorus i a, w (reflection i a x) ≤ w x) (x : Torus d) :
    pairMoment i a f w x ≤ pairMoment i a (polarize i a f) w x := by
  rcases reflection_half_or_fixed i a x with hfix | hside
  · simp [pairMoment, polarize_of_fixed i a f hfix, hfix]
  · by_cases hx : x ∈ halfTorus i a
    · exact pairMoment_polarize_le_on_half i a f w hx (hw x hx)
    · have hr := hside.mpr hx
      have h := pairMoment_polarize_le_on_half i a f w hr (hw _ hr)
      simpa only [pairMoment_reflect] using h

theorem polarize_eq_of_pairMoment_eq_on_half {d : ℕ} (i : Fin d) (a : ℝ)
    (f w : Torus d → ℝ) {x : Torus d} (hx : x ∈ halfTorus i a)
    (hw : w (reflection i a x) < w x)
    (he : pairMoment i a f w x = pairMoment i a (polarize i a f) w x) :
    polarize i a f x = f x := by
  have hle : f (reflection i a x) ≤ f x := by
    by_contra h
    have hlt := lt_of_not_ge h
    unfold pairMoment at he
    rw [polarize_reflected_of_mem i a f hx] at he
    simp only [polarize, if_pos hx, max_eq_right hlt.le, min_eq_left hlt.le] at he
    have hp := mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hw)
    nlinarith
  simp [polarize, hx, hle]

theorem polarize_eq_of_pairMoment_eq {d : ℕ} (i : Fin d) (a : ℝ)
    (f w : Torus d → ℝ)
    (hw : ∀ x ∈ halfTorus i a, reflection i a x ≠ x → w (reflection i a x) < w x)
    (x : Torus d) (he : pairMoment i a f w x = pairMoment i a (polarize i a f) w x) :
    polarize i a f x = f x := by
  rcases reflection_half_or_fixed i a x with hfix | hside
  · exact polarize_of_fixed i a f hfix
  · by_cases hfix : reflection i a x = x
    · exact polarize_of_fixed i a f hfix
    · by_cases hx : x ∈ halfTorus i a
      · exact polarize_eq_of_pairMoment_eq_on_half i a f w hx (hw x hx hfix) he
      · have hr := hside.mpr hx
        have hnr : reflection i a (reflection i a x) ≠ reflection i a x := by
          rw [reflection_involutive]
          exact Ne.symm hfix
        have her : pairMoment i a f w (reflection i a x) =
            pairMoment i a (polarize i a f) w (reflection i a x) := by
          simpa only [pairMoment_reflect] using he
        have hp := polarize_eq_of_pairMoment_eq_on_half i a f w hr (hw _ hr hnr) her
        have hs := polarize_pair i a f id x
        dsimp only [id_eq] at hs
        linarith

theorem pairMoment_integrable {d : ℕ} (i : Fin d) (a : ℝ) {f w : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hw : MemLp w 2 (torusMeasure d)) :
    Integrable (pairMoment i a f w) (torusMeasure d) :=
  (hf.integrable_mul hw).add (reflection_integrable i a (hf.integrable_mul hw))

theorem integral_pairMoment {d : ℕ} (i : Fin d) (a : ℝ) {f w : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hw : MemLp w 2 (torusMeasure d)) :
    (∫ x, pairMoment i a f w x ∂torusMeasure d) = 2*(∫ x, f x*w x ∂torusMeasure d) := by
  have hfw : Integrable (fun x => f x*w x) (torusMeasure d) := hf.integrable_mul hw
  unfold pairMoment
  rw [integral_add hfw (reflection_integrable i a hfw)]
  have h := reflection_integral i a (fun x => f x*w x)
  change (∫ x, f (reflection i a x)*w (reflection i a x) ∂torusMeasure d) = _ at h
  rw [h]
  ring

theorem moment_polarize_le {d : ℕ} (i : Fin d) (a : ℝ) {f w : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hw : MemLp w 2 (torusMeasure d))
    (hmono : ∀ x ∈ halfTorus i a, w (reflection i a x) ≤ w x) :
    (∫ x, f x*w x ∂torusMeasure d) ≤ ∫ x, polarize i a f x*w x ∂torusMeasure d := by
  have h := integral_mono_ae (pairMoment_integrable i a hf hw)
    (pairMoment_integrable i a (polarize_memLp_two i a hf) hw)
    (Filter.Eventually.of_forall (pairMoment_polarize_le i a f w hmono))
  rw [integral_pairMoment i a hf hw, integral_pairMoment i a (polarize_memLp_two i a hf) hw] at h
  linarith

theorem polarize_ae_eq_of_moment_eq {d : ℕ} (i : Fin d) (a : ℝ) {f w : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hw : MemLp w 2 (torusMeasure d))
    (hstrict : ∀ x ∈ halfTorus i a, reflection i a x ≠ x → w (reflection i a x) < w x)
    (he : (∫ x, f x*w x ∂torusMeasure d) = ∫ x, polarize i a f x*w x ∂torusMeasure d) :
    polarize i a f =ᵐ[torusMeasure d] f := by
  have hmono (x : Torus d) (hx : x ∈ halfTorus i a) : w (reflection i a x) ≤ w x := by
    by_cases hfix : reflection i a x = x
    · rw [hfix]
    · exact (hstrict x hx hfix).le
  have hpe : (∫ x, pairMoment i a f w x ∂torusMeasure d) =
      ∫ x, pairMoment i a (polarize i a f) w x ∂torusMeasure d := by
    rw [integral_pairMoment i a hf hw, integral_pairMoment i a (polarize_memLp_two i a hf) hw, he]
  have hae := (integral_eq_iff_of_ae_le (pairMoment_integrable i a hf hw)
    (pairMoment_integrable i a (polarize_memLp_two i a hf) hw)
    (Filter.Eventually.of_forall (pairMoment_polarize_le i a f w hmono))).mp hpe
  filter_upwards [hae] with x hx
  exact polarize_eq_of_pairMoment_eq i a f w hstrict x hx

#print axioms moment_polarize_le
#print axioms polarize_ae_eq_of_moment_eq
end Legacy.BecknerOnofri.CoordinatePolarization

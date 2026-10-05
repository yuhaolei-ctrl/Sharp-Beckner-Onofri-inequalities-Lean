import Legacy.BecknerOnofri.CoordinatePolarization

/-! The actual four-point polarization inequality and its Haar integral consequence. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.CoordinatePolarization
attribute [local instance] Classical.propDecidable

theorem sorted_pair_weighted_le (α β u v r s : ℝ) (hα : β ≤ α) :
    α*(u*r+v*s)+β*(u*s+v*r) ≤
      α*(max u v*max r s+min u v*min r s)+β*(max u v*min r s+min u v*max r s) := by
  rcases le_total u v with huv | hvu <;> rcases le_total r s with hrs | hsr
  · simp [huv, hrs]
    ring_nf
    rfl
  · simp [huv, hsr]
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) (mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hsr))]
  · simp [hvu, hrs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) (mul_nonneg (sub_nonneg.mpr hvu) (sub_nonneg.mpr hrs))]
  · simp [hvu, hsr]

def fourPoint {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ) (f : Torus d → ℝ)
    (x y : Torus d) : ℝ :=
  K x y*f x*f y + K x (reflection i a y)*f x*f (reflection i a y) +
  K (reflection i a x) y*f (reflection i a x)*f y +
  K (reflection i a x) (reflection i a y)*f (reflection i a x)*f (reflection i a y)

theorem fourPoint_reflect_left {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (f : Torus d → ℝ) (x y : Torus d) :
    fourPoint i a K f (reflection i a x) y = fourPoint i a K f x y := by
  unfold fourPoint
  rw [reflection_involutive]
  ring

theorem fourPoint_reflect_right {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (f : Torus d → ℝ) (x y : Torus d) :
    fourPoint i a K f x (reflection i a y) = fourPoint i a K f x y := by
  unfold fourPoint
  rw [reflection_involutive]
  ring

theorem polarize_of_fixed {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) {x : Torus d}
    (hx : reflection i a x = x) : polarize i a f x = f x := by simp [polarize, hx]

theorem polarize_reflected_of_mem {d : ℕ} (i : Fin d) (a : ℝ) (f : Torus d → ℝ) {x : Torus d}
    (hx : x ∈ halfTorus i a) : polarize i a f (reflection i a x) = min (f x) (f (reflection i a x)) := by
  rcases reflection_half_or_fixed i a x with hfix | hside
  · simp [polarize, hfix]
  · have hr : reflection i a x ∉ halfTorus i a := by simpa [hx] using hside
    simp only [polarize, if_neg hr]
    rw [reflection_involutive i a x]
    exact min_comm _ _

theorem fourPoint_reduced {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (f : Torus d → ℝ) (x y : Torus d) :
    fourPoint i a K f x y = K x y*(f x*f y+f (reflection i a x)*f (reflection i a y))+
      K x (reflection i a y)*(f x*f (reflection i a y)+f (reflection i a x)*f y) := by
  have hh := hK x (reflection i a y)
  rw [reflection_involutive] at hh
  unfold fourPoint
  rw [hK, hh]
  ring

theorem fourPoint_polarize_le_on_half {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (hmono : ∀ x ∈ halfTorus i a, ∀ y ∈ halfTorus i a, K x (reflection i a y) ≤ K x y)
    (f : Torus d → ℝ) {x y : Torus d} (hx : x ∈ halfTorus i a) (hy : y ∈ halfTorus i a) :
    fourPoint i a K f x y ≤ fourPoint i a K (polarize i a f) x y := by
  rw [fourPoint_reduced i a K hK, fourPoint_reduced i a K hK,
    polarize_reflected_of_mem i a f hx, polarize_reflected_of_mem i a f hy]
  simp only [polarize, if_pos hx, if_pos hy]
  exact sorted_pair_weighted_le _ _ _ _ _ _ (hmono x hx y hy)

theorem fourPoint_polarize_eq_of_fixed_left {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (f : Torus d → ℝ) {x : Torus d} (hx : reflection i a x = x) (y : Torus d) :
    fourPoint i a K f x y = fourPoint i a K (polarize i a f) x y := by
  have hpair := polarize_pair i a f id y
  dsimp only [id_eq] at hpair
  have hh := hK x y
  rw [hx] at hh
  simp only [fourPoint, hx, hh, polarize_of_fixed i a f hx]
  have he := congrArg (fun r : ℝ => 2*K x y*f x*r) hpair
  nlinarith only [he]

theorem fourPoint_polarize_eq_of_fixed_right {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (f : Torus d → ℝ) (x : Torus d) {y : Torus d} (hy : reflection i a y = y) :
    fourPoint i a K f x y = fourPoint i a K (polarize i a f) x y := by
  have hpair := polarize_pair i a f id x
  dsimp only [id_eq] at hpair
  have hh := hK x y
  rw [hy] at hh
  simp only [fourPoint, hy, hh, polarize_of_fixed i a f hy]
  have he := congrArg (fun r : ℝ => 2*K x y*f y*r) hpair
  nlinarith only [he]

/-- A genuine pointwise four-point inequality, valid also on the two fixed coordinate hyperplanes. -/
theorem fourPoint_polarize_le {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (hmono : ∀ x ∈ halfTorus i a, ∀ y ∈ halfTorus i a, K x (reflection i a y) ≤ K x y)
    (f : Torus d → ℝ) (x y : Torus d) :
    fourPoint i a K f x y ≤ fourPoint i a K (polarize i a f) x y := by
  rcases reflection_half_or_fixed i a x with hfix | hside
  · exact (fourPoint_polarize_eq_of_fixed_left i a K hK f hfix y).le
  rcases reflection_half_or_fixed i a y with hfix | hsidey
  · exact (fourPoint_polarize_eq_of_fixed_right i a K hK f x hfix).le
  by_cases hx : x ∈ halfTorus i a <;> by_cases hy : y ∈ halfTorus i a
  · exact fourPoint_polarize_le_on_half i a K hK hmono f hx hy
  · simpa only [fourPoint_reflect_right] using
      fourPoint_polarize_le_on_half i a K hK hmono f hx (hsidey.mpr hy)
  · simpa only [fourPoint_reflect_left] using
      fourPoint_polarize_le_on_half i a K hK hmono f (hside.mpr hx) hy
  · simpa only [fourPoint_reflect_left, fourPoint_reflect_right] using
      fourPoint_polarize_le_on_half i a K hK hmono f (hside.mpr hx) (hsidey.mpr hy)

#print axioms fourPoint_polarize_le
end Legacy.BecknerOnofri.CoordinatePolarization

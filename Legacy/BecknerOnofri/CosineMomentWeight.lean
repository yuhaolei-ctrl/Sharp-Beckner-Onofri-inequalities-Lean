module

public import Legacy.BecknerOnofri.PolarizationSelection

@[expose] public section

/-! The actual sum of coordinate cosines is a strict polarization weight for
every semicircle containing the origin in its interior. -/
noncomputable section
namespace Legacy.BecknerOnofri.CosineMomentWeight
open MeasureTheory Set Legacy.TorusEndpoint CoordinatePolarization
open scoped BigOperators

def circleCos (x : UnitAddCircle) : ℝ := (fourier 1 x).re

theorem circleCos_continuous : Continuous circleCos := Complex.continuous_re.comp (fourier 1).continuous

theorem circleCos_coe (t : ℝ) : circleCos (t : UnitAddCircle) = Real.cos (2*Real.pi*t) := by
  unfold circleCos
  rw [fourier_coe_apply]
  simp [Complex.exp_re]

theorem circleReflection_coe (a t : ℝ) :
    circleReflection a (t : UnitAddCircle) = ((2*a-t : ℝ) : UnitAddCircle) := by
  rw [AddCircle.coe_sub]
  rfl

theorem circleReflection_midpoint (a : ℝ) :
    circleReflection a ((a+1/2 : ℝ) : UnitAddCircle) = ((a+1/2 : ℝ) : UnitAddCircle) := by
  rw [circleReflection_coe]
  have h := AddCircle.coe_add_period 1 (2*a-(a+1/2))
  convert! h.symm using 1
  congr 1
  ring

theorem circleCos_reflection_lt {a : ℝ} (ha : -(1/2:ℝ) < a) (ha0 : a < 0)
    {x : UnitAddCircle} (hx : x ∈ circleHalf a) (hfix : circleReflection a x ≠ x) :
    circleCos (circleReflection a x) < circleCos x := by
  rw [circleHalf_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htm : t < a+1/2 := lt_of_le_of_ne ht.2 (by
    intro he
    subst t
    exact hfix (circleReflection_midpoint a))
  rw [circleReflection_coe, circleCos_coe, circleCos_coe]
  have hA : Real.sin (2*Real.pi*a) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hB : 0 < Real.sin (2*Real.pi*(t-a)) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos])
  rw [show 2*Real.pi*(2*a-t) = 2*Real.pi*a-2*Real.pi*(t-a) by ring,
    show 2*Real.pi*t = 2*Real.pi*a+2*Real.pi*(t-a) by ring, Real.cos_sub, Real.cos_add]
  nlinarith [mul_neg_of_neg_of_pos hA hB]

def weight (d : ℕ) (x : Torus d) : ℝ := ∑ i, circleCos (x i)

theorem weight_continuous (d : ℕ) : Continuous (weight d) := by
  unfold weight
  exact continuous_finsetSum _ (fun i _ => circleCos_continuous.comp (continuous_apply i))

theorem weight_memLp (d : ℕ) : MemLp (weight d) 2 (torusMeasure d) :=
  (weight_continuous d).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem weight_reflection_difference {d : ℕ} (i : Fin d) (a : ℝ) (x : Torus d) :
    weight d (reflection i a x)-weight d x = circleCos (circleReflection a (x i))-circleCos (x i) := by
  unfold weight
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [reflection]
  · intro j _ hji
    simp [reflection, hji]
  · simp

theorem weight_strict {d : ℕ} (i : Fin d) {a : ℝ}
    (ha : -(1/2:ℝ) < a) (ha0 : a < 0) (x : Torus d) (hx : x ∈ halfTorus i a)
    (hfix : reflection i a x ≠ x) : weight d (reflection i a x) < weight d x := by
  have hcircle : circleReflection a (x i) ≠ x i := by
    intro h
    apply hfix
    funext j
    by_cases hj : j = i
    · subst j
      simpa [reflection] using h
    · simp [reflection, hj]
  have h := circleCos_reflection_lt ha ha0 hx hcircle
  have he := weight_reflection_difference i a x
  linarith

#print axioms weight_strict
end Legacy.BecknerOnofri.CosineMomentWeight

module

public import Legacy.BecknerOnofri.PolarizationContinuous

@[expose] public section

/-! Actual coordinatewise symmetry and monotonicity follow from all
origin-directed polarization fixed points. -/
noncomputable section
namespace Legacy.BecknerOnofri.SteinerFromPolarization
open MeasureTheory Set Filter Legacy.TorusEndpoint CoordinatePolarization
open scoped Topology

def slice {d : ℕ} (x : Torus d) (i : Fin d) (t : ℝ) : Torus d :=
  Function.update x i (t : UnitAddCircle)

theorem slice_continuous {d : ℕ} (x : Torus d) (i : Fin d) : Continuous (slice x i) :=
  continuous_const.update i (AddCircle.continuous_mk' 1)

theorem slice_reflection {d : ℕ} (x : Torus d) (i : Fin d) (a s : ℝ) :
    reflection i a (slice x i s) = slice x i (2*a-s) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [slice, reflection, CosineMomentWeight.circleReflection_coe]
  · simp [slice, reflection, hj]

theorem slice_sub_one {d : ℕ} (x : Torus d) (i : Fin d) (t : ℝ) :
    slice x i (t-1) = slice x i t := by
  have hc : ((t-1 : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
    have h := AddCircle.coe_add_period 1 (t-1)
    convert! h.symm using 1
    congr 1
    ring
  simp [slice, hc]

theorem slice_comparison {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (x : Torus d) (i : Fin d) {a s : ℝ}
    (ha : -(1/2:ℝ) < a) (ha0 : a < 0) (hs : a < s) (hsh : s ≤ a+1/2) :
    f (slice x i (2*a-s)) ≤ f (slice x i s) := by
  have hx : slice x i s ∈ halfTorus i a := by
    change (Function.update x i (s : UnitAddCircle)) i ∈ circleHalf a
    simp only [Function.update_self]
    rw [circleHalf_eq_image]
    exact ⟨s, ⟨hs, hsh⟩, rfl⟩
  have h := origin_fixed_reflection_ge hf hfixed i ha ha0 hx
  rwa [slice_reflection] at h

theorem slice_antitone {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (x : Torus d) (i : Fin d) :
    AntitoneOn (fun t : ℝ => f (slice x i t)) (Icc 0 (1/2)) := by
  intro s hs t ht hst
  by_cases he : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst he
  have h := slice_comparison hf hfixed x i (a := (s+t)/2-1/2) (s := s)
    (by linarith [hs.1]) (by linarith [ht.2]) (by linarith [hs.1, ht.2]) (by linarith)
  rw [show 2*((s+t)/2-1/2)-s = t-1 by ring, slice_sub_one] at h
  exact h

theorem cross_negative_le_positive {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (x : Torus d) (i : Fin d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1/2) :
    f (slice x i (-t)) ≤ f (slice x i s) := by
  have h := slice_comparison hf hfixed x i (a := (s-t)/2) (s := s)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rwa [show 2*((s-t)/2)-s = -t by ring] at h

theorem cross_positive_le_negative {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (x : Torus d) (i : Fin d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1/2) :
    f (slice x i t) ≤ f (slice x i (-s)) := by
  have h := slice_comparison hf hfixed x i (a := (t-s)/2-1/2) (s := -s)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [show 2*((t-s)/2-1/2)-(-s) = t-1 by ring, slice_sub_one] at h
  exact h

theorem slice_even {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (x : Torus d) (i : Fin d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1/2) : f (slice x i t) = f (slice x i (-t)) := by
  by_cases htzero : t = 0
  · simp [htzero]
  have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  let s : ℕ → ℝ := fun n => t*(1-(1/2:ℝ)^n)
  have hs0 (n : ℕ) : 0 ≤ s n :=
    mul_nonneg ht0 (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)))
  have hst (n : ℕ) : s n < t := by
    have hp : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _
    dsimp [s]
    nlinarith [mul_pos htp hp]
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Tendsto s atTop (𝓝 t) := by
    convert! (tendsto_const_nhds.mul (tendsto_const_nhds.sub hp) :
      Tendsto (fun n : ℕ => t*(1-(1/2:ℝ)^n)) atTop (𝓝 (t*(1-0)))) using 1
    simp
  have hc : Continuous (fun r : ℝ => f (slice x i r)) := hf.comp (slice_continuous x i)
  have hleft : f (slice x i (-t)) ≤ f (slice x i t) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hc.continuousAt.tendsto.comp hs)
      (Filter.Eventually.of_forall (fun n => cross_negative_le_positive hf hfixed x i
        (s := s n) (t := t) (hs0 n) (hst n) ht))
  have hright : f (slice x i t) ≤ f (slice x i (-t)) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ((hc.comp continuous_neg).continuousAt.tendsto.comp hs)
      (Filter.Eventually.of_forall (fun n => cross_positive_le_negative hf hfixed x i
        (s := s n) (t := t) (hs0 n) (hst n) ht))
  exact le_antisymm hright hleft

theorem separately_even {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) (i : Fin d) (x : Torus d) :
    f (Function.update x i (-x i)) = f x := by
  let t : ℝ := AddCircle.equivIoc 1 (-(1/2:ℝ)) (x i)
  have ht : -(1/2:ℝ) < t ∧ t ≤ 1/2 := by
    have h := (AddCircle.equivIoc 1 (-(1/2:ℝ)) (x i)).property
    constructor
    · exact h.1
    · linarith [h.2]
  have hx : (t : UnitAddCircle) = x i := AddCircle.coe_equivIoc
  have he : f (slice x i (-t)) = f (slice x i t) := by
    by_cases hp : 0 ≤ t
    · exact (slice_even hf hfixed x i hp ht.2).symm
    · have h := slice_even hf hfixed x i (t := -t) (by linarith) (by linarith [ht.1])
      simpa using h
  simpa [slice, AddCircle.coe_neg, hx] using he

#print axioms slice_antitone
#print axioms separately_even
end Legacy.BecknerOnofri.SteinerFromPolarization

import Legacy.BecknerOnofri.HeatDensityApproximation

/-! Actual circle half-arcs and measure-preserving coordinate reflections on the Haar torus. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.CoordinatePolarization

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance

def circleReflection (a : ℝ) (x : UnitAddCircle) : UnitAddCircle := ((2*a : ℝ) : UnitAddCircle)-x

def circleHalf (a : ℝ) : Set UnitAddCircle :=
  {x | (AddCircle.equivIoc 1 a x : ℝ) ≤ a+1/2}

theorem circleHalf_measurable (a : ℝ) : MeasurableSet (circleHalf a) :=
  measurableSet_le (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 a).measurable) measurable_const

/-- The selected side is the actual half-open half-circle, the quotient image of a real interval. -/
theorem circleHalf_eq_image (a : ℝ) : circleHalf a =
    (fun t : ℝ => (t : UnitAddCircle)) '' Ioc a (a+1/2) := by
  ext x
  constructor
  · intro hx
    refine ⟨(AddCircle.equivIoc 1 a x : ℝ), ⟨(AddCircle.equivIoc 1 a x).property.1, hx⟩, ?_⟩
    exact AddCircle.coe_equivIoc
  · rintro ⟨t, ht, rfl⟩
    change (AddCircle.equivIoc 1 a (t : UnitAddCircle) : ℝ) ≤ a+1/2
    rw [AddCircle.equivIoc_coe_eq (show t ∈ Ioc a (a+1) by constructor; exact ht.1; linarith [ht.2])]
    exact ht.2

theorem circleReflection_involutive (a : ℝ) : Function.Involutive (circleReflection a) := by
  intro x
  simp [circleReflection]

theorem circleReflection_measurePreserving (a : ℝ) :
    MeasurePreserving (circleReflection a) (AddCircle.haarAddCircle (T := 1)) (AddCircle.haarAddCircle (T := 1)) :=
  Measure.measurePreserving_sub_left _ _

/-- Only fixed boundary points fail to exchange the selected and unselected semicircles. -/
theorem circleReflection_half_or_fixed (a : ℝ) (x : UnitAddCircle) :
    circleReflection a x = x ∨ (circleReflection a x ∈ circleHalf a ↔ x ∉ circleHalf a) := by
  let r : ℝ := AddCircle.equivIoc 1 a x
  have hr : a < r ∧ r ≤ a+1 := (AddCircle.equivIoc 1 a x).property
  have hrx : (r : UnitAddCircle) = x := AddCircle.coe_equivIoc
  by_cases hend : r = a+1
  · left
    have hxa : x = (a : UnitAddCircle) := by rw [← hrx, hend, AddCircle.coe_add_period]
    rw [hxa]
    unfold circleReflection
    rw [show 2*a=a+a by ring, AddCircle.coe_add]
    abel
  · have hrl : r < a+1 := lt_of_le_of_ne hr.2 hend
    let q : ℝ := 2*a+1-r
    have hq : q ∈ Ioc a (a+1) := by dsimp [q]; constructor <;> linarith
    have hqx : (q : UnitAddCircle) = circleReflection a x := by
      calc
        (q : UnitAddCircle) = ((2*a-r : ℝ) : UnitAddCircle) := by
          convert! AddCircle.coe_add_period 1 (2*a-r) using 1
          congr 1
          dsimp [q]
          ring
        _ = circleReflection a x := by rw [AddCircle.coe_sub, hrx]; rfl
    have hrep : (AddCircle.equivIoc 1 a (circleReflection a x) : ℝ) = q := by
      rw [← hqx, AddCircle.equivIoc_coe_eq hq]
    by_cases hmid : r = a+1/2
    · left
      have hqr : q = r := by dsimp [q]; linarith
      rw [← hqx, hqr, hrx]
    · right
      change ((AddCircle.equivIoc 1 a (circleReflection a x) : ℝ) ≤ a+1/2) ↔ ¬r ≤ a+1/2
      rw [hrep]
      dsimp [q]
      constructor
      · intro h hh
        apply hmid
        linarith
      · intro h
        push Not at h
        linarith

def reflection {d : ℕ} (i : Fin d) (a : ℝ) (x : Torus d) : Torus d :=
  fun j => if j=i then circleReflection a (x j) else x j

def halfTorus {d : ℕ} (i : Fin d) (a : ℝ) : Set (Torus d) := {x | x i ∈ circleHalf a}

theorem halfTorus_measurable {d : ℕ} (i : Fin d) (a : ℝ) : MeasurableSet (halfTorus i a) :=
  (circleHalf_measurable a).preimage (measurable_pi_apply i)

theorem reflection_continuous {d : ℕ} (i : Fin d) (a : ℝ) : Continuous (reflection i a) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · simp only [reflection, if_pos hj, circleReflection]
    exact continuous_const.sub (continuous_apply j : Continuous (fun x : Torus d => x j))
  · simpa only [reflection, if_neg hj] using (continuous_apply j : Continuous (fun x : Torus d => x j))

theorem reflection_involutive {d : ℕ} (i : Fin d) (a : ℝ) : Function.Involutive (reflection i a) := by
  intro x
  funext j
  by_cases hj : j=i
  · simp only [reflection, if_pos hj]
    exact circleReflection_involutive a (x j)
  · simp [reflection, hj]

def reflectionEquiv {d : ℕ} (i : Fin d) (a : ℝ) : Torus d ≃ᵐ Torus d where
  toFun := reflection i a
  invFun := reflection i a
  left_inv := reflection_involutive i a
  right_inv := reflection_involutive i a
  measurable_toFun := (reflection_continuous i a).measurable
  measurable_invFun := (reflection_continuous i a).measurable

theorem reflection_measurePreserving {d : ℕ} (i : Fin d) (a : ℝ) :
    MeasurePreserving (reflection i a) (torusMeasure d) (torusMeasure d) := by
  rw [torusMeasure_explicit]
  exact measurePreserving_pi _ _ (f := fun j (x : UnitAddCircle) => if j=i then circleReflection a x else x) (by
    intro j
    by_cases hj : j=i
    · simpa only [if_pos hj] using circleReflection_measurePreserving a
    · simpa only [if_neg hj] using! MeasurePreserving.id (AddCircle.haarAddCircle (T := 1)))

theorem reflection_half_or_fixed {d : ℕ} (i : Fin d) (a : ℝ) (x : Torus d) :
    reflection i a x = x ∨ (reflection i a x ∈ halfTorus i a ↔ x ∉ halfTorus i a) := by
  rcases circleReflection_half_or_fixed a (x i) with hx | hx
  · left
    funext j
    by_cases hj : j=i
    · subst j
      simp [reflection, hx]
    · simp [reflection, hj]
  · right
    simpa [halfTorus, reflection] using hx

#print axioms reflection_measurePreserving
#print axioms reflection_half_or_fixed
end Legacy.BecknerOnofri.CoordinatePolarization

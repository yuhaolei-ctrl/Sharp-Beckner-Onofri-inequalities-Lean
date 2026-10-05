import BecknerOnofri.Definitions
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual real-valued coordinate averaging on normalized product Haar space. -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.EntropyShearer

/-- A measurable real function with an everywhere uniform bound. -/
def BoundedMeasurable {d : ℕ} (f : Torus d → ℝ) : Prop :=
  Measurable f ∧ ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B

/-- Integrate exactly the coordinates in `s`. The remaining coordinates are
actual arguments of the density, so deleting coordinate `i` means `avg {i}`. -/
def avg {d : ℕ} (s : Finset (Fin d)) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y : s → UnitAddCircle, f (updateFinset x s y)
    ∂Measure.pi (fun _ : s => AddCircle.haarAddCircle)

theorem BoundedMeasurable.integrable {d : ℕ} {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) : Integrable f (torusMeasure d) := by
  obtain ⟨hm, B, hB⟩ := hf
  exact (integrable_const B).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hB)

theorem avg_measurable {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : Measurable f) : Measurable (avg s f) :=
  (hf.comp measurable_updateFinset').stronglyMeasurable.integral_prod_right'.measurable

theorem avg_norm_bound {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ} {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (x : Torus d) : ‖avg s f x‖ ≤ B := by
  simpa [avg] using norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : s => AddCircle.haarAddCircle))
    (Filter.Eventually.of_forall (fun y => hB (updateFinset x s y)))

theorem BoundedMeasurable.avg {d : ℕ} {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) (s : Finset (Fin d)) : BoundedMeasurable (avg s f) := by
  obtain ⟨hm, B, hB⟩ := hf
  exact ⟨avg_measurable s hm, B, avg_norm_bound s hB⟩

@[simp] theorem avg_empty {d : ℕ} (f : Torus d → ℝ) : avg ∅ f = f := by
  funext x
  simp only [avg, updateFinset_empty, integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem avg_const {d : ℕ} (s : Finset (Fin d)) (c : ℝ) :
    avg s (fun _ : Torus d => c) = fun _ => c := by
  funext x
  simp [avg]

theorem avg_update {d : ℕ} (s : Finset (Fin d)) (f : Torus d → ℝ)
    (x : Torus d) (y : s → UnitAddCircle) :
    avg s f (updateFinset x s y) = avg s f x := by
  unfold avg
  simp only [updateFinset_updateFinset_of_subset (Finset.Subset.refl s)]

@[simp] theorem avg_idem {d : ℕ} (s : Finset (Fin d)) (f : Torus d → ℝ) :
    avg s (avg s f) = avg s f := by
  funext x
  change (∫ y : s → UnitAddCircle, avg s f (updateFinset x s y)
    ∂Measure.pi (fun _ : s => AddCircle.haarAddCircle)) = avg s f x
  simp only [avg_update, integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem avg_union {d : ℕ} {s t : Finset (Fin d)} (hst : Disjoint s t)
    {f : Torus d → ℝ} (hf : BoundedMeasurable f) :
    avg (s ∪ t) f = avg s (avg t f) := by
  funext x
  let e := MeasurableEquiv.piFinsetUnion (fun _ : Fin d => UnitAddCircle) hst
  have hi : Integrable (fun y : (s → UnitAddCircle) × (t → UnitAddCircle) =>
      f (updateFinset x (s ∪ t) (e y)))
      ((Measure.pi (fun _ : s => AddCircle.haarAddCircle)).prod
        (Measure.pi (fun _ : t => AddCircle.haarAddCircle))) := by
    obtain ⟨hm, B, hB⟩ := hf
    apply (integrable_const B).mono'
      ((hm.comp (measurable_updateFinset.comp e.measurable)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun y => hB _)
  calc
    _ = ∫ y : (s → UnitAddCircle) × (t → UnitAddCircle),
        f (updateFinset x (s ∪ t) (e y))
        ∂(Measure.pi (fun _ : s => AddCircle.haarAddCircle)).prod
          (Measure.pi (fun _ : t => AddCircle.haarAddCircle)) :=
      ((measurePreserving_piFinsetUnion hst (fun _ : Fin d => AddCircle.haarAddCircle)).integral_comp'
        (fun z => f (updateFinset x (s ∪ t) z))).symm
    _ = _ := by
      rw [integral_prod _ hi]
      simp only [avg, updateFinset_updateFinset hst]
      rfl

@[simp] theorem avg_univ {d : ℕ} (f : Torus d → ℝ) :
    avg Finset.univ f = fun _ => ∫ x, f x ∂torusMeasure d := by
  let e : {j : Fin d // j ∈ Finset.univ} ≃ Fin d := Equiv.subtypeUnivEquiv Finset.mem_univ
  funext x
  have h := (measurePreserving_piCongrLeft
    (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) e).integral_comp' f
  change (∫ y : Finset.univ → UnitAddCircle, f (updateFinset x Finset.univ y)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _
  unfold torusMeasure
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change f (updateFinset x Finset.univ y) =
      f ((MeasurableEquiv.piCongrLeft (fun _ : Fin d => UnitAddCircle) e) y)
    apply congrArg f
    funext i
    rw [updateFinset_univ_apply]
    exact (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin d => UnitAddCircle) e y ⟨i, Finset.mem_univ i⟩).symm)

theorem integral_avg {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) :
    (∫ x, avg s f x ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d := by
  have hu : sᶜ ∪ s = Finset.univ := by rw [Finset.union_comm, Finset.union_compl]
  have h1 := avg_union (s := sᶜ) (t := s) (by
    exact Finset.disjoint_left.mpr (fun i hi h => (Finset.mem_compl.mp hi) h)) hf
  have h2 := avg_union (s := sᶜ) (t := s) (by
    exact Finset.disjoint_left.mpr (fun i hi h => (Finset.mem_compl.mp hi) h)) (hf.avg s)
  rw [hu, avg_univ] at h1 h2
  rw [avg_idem] at h2
  have he : (fun _ : Torus d => ∫ x, avg s f x ∂torusMeasure d) =
      (fun _ : Torus d => ∫ x, f x ∂torusMeasure d) := h2.trans h1.symm
  exact congrFun he 0

theorem BoundedMeasurable.const {d : ℕ} (c : ℝ) :
    BoundedMeasurable (fun _ : Torus d => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

theorem BoundedMeasurable.mul {d : ℕ} {f g : Torus d → ℝ}
    (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable (fun x => f x * g x) := by
  obtain ⟨hfm, B, hB⟩ := hf
  obtain ⟨hgm, C, hC⟩ := hg
  refine ⟨hfm.mul hgm, B * C, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hB x) (hC x) (norm_nonneg _) ((norm_nonneg _).trans (hB x))

theorem BoundedMeasurable.add {d : ℕ} {f g : Torus d → ℝ}
    (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable (fun x => f x + g x) := by
  obtain ⟨hfm, B, hB⟩ := hf
  obtain ⟨hgm, C, hC⟩ := hg
  exact ⟨hfm.add hgm, B + C, fun x => (norm_add_le _ _).trans (add_le_add (hB x) (hC x))⟩

theorem BoundedMeasurable.sub {d : ℕ} {f g : Torus d → ℝ}
    (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable (fun x => f x - g x) := by
  obtain ⟨hfm, B, hB⟩ := hf
  obtain ⟨hgm, C, hC⟩ := hg
  exact ⟨hfm.sub hgm, B + C, fun x => (norm_sub_le _ _).trans (add_le_add (hB x) (hC x))⟩

theorem integral_pairing {d : ℕ} (s : Finset (Fin d)) {f g : Torus d → ℝ}
    (hf : BoundedMeasurable f) (hg : BoundedMeasurable g)
    (hInv : ∀ x y, g (updateFinset x s y) = g x) :
    (∫ x, f x * g x ∂torusMeasure d) =
      ∫ x, avg s f x * g x ∂torusMeasure d := by
  rw [← integral_avg s (hf.mul hg)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change (∫ y : s → UnitAddCircle, f (updateFinset x s y) * g (updateFinset x s y)
      ∂Measure.pi (fun _ : s => AddCircle.haarAddCircle)) = avg s f x * g x
    simp only [hInv, integral_mul_const, avg])

theorem avg_singleton {d : ℕ} (i : Fin d) (f : Torus d → ℝ) :
    avg {i} f = fun x => ∫ y, f (Function.update x i y) ∂AddCircle.haarAddCircle := by
  let α : Type := ({i} : Finset (Fin d))
  let e := (MeasurableEquiv.piUnique fun _ : α => UnitAddCircle).symm
  funext x
  have h := (measurePreserving_piUnique
    (fun _ : α => (AddCircle.haarAddCircle : Measure UnitAddCircle))).symm e.symm
  have hi := h.integral_comp' (fun y => f (updateFinset x {i} y))
  simpa [avg, e, α, update_eq_updateFinset] using hi.symm

end BecknerOnofri.HighDim.EntropyShearer

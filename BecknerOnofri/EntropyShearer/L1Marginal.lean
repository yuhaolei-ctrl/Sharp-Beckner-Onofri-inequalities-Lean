module

public import BecknerOnofri.EntropyShearer.Chain

@[expose] public section

/-! Haar marginalization on the full L1 domain. The redundant coordinates in
this full-torus integral have probability mass one. -/
noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyShearer

def mix {d : ℕ} (s : Finset (Fin d)) (z : Torus d × Torus d) : Torus d :=
  fun i => if i ∈ s then z.2 i else z.1 i

def fullAvg {d : ℕ} (s : Finset (Fin d)) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, f (mix s (x,y)) ∂torusMeasure d

lemma mix_measurePreserving {d : ℕ} (s : Finset (Fin d)) :
    MeasurePreserving (mix s) ((torusMeasure d).prod (torusMeasure d)) (torusMeasure d) := by
  let μ : Fin d → Measure UnitAddCircle := fun _ => AddCircle.haarAddCircle
  let e := MeasurableEquiv.arrowProdEquivProdArrow UnitAddCircle UnitAddCircle (Fin d)
  have he : MeasurePreserving e.symm ((torusMeasure d).prod (torusMeasure d))
      (Measure.pi (fun i => (μ i).prod (μ i))) :=
    (measurePreserving_arrowProdEquivProdArrow UnitAddCircle UnitAddCircle (Fin d) μ μ).symm e
  have hm : MeasurePreserving (fun z : Fin d → UnitAddCircle × UnitAddCircle =>
      fun i => if i ∈ s then (z i).2 else (z i).1)
      (Measure.pi (fun i => (μ i).prod (μ i))) (torusMeasure d) := by
    apply measurePreserving_pi (fun i => (μ i).prod (μ i)) μ
      (f := fun i z => if i ∈ s then z.2 else z.1)
    intro i
    by_cases hi : i ∈ s
    · simpa only [hi, if_true] using (measurePreserving_snd (μ := μ i) (ν := μ i))
    · simpa only [hi, if_false] using (measurePreserving_fst (μ := μ i) (ν := μ i))
  exact hm.comp he

lemma mix_integrable {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    Integrable (fun z => f (mix s z)) ((torusMeasure d).prod (torusMeasure d)) :=
  (mix_measurePreserving s).integrable_comp_of_integrable hf

lemma fullAvg_integrable {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) : Integrable (fullAvg s f) (torusMeasure d) :=
  (mix_integrable s hf).integral_prod_left

lemma integral_fullAvg {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    (∫ x, fullAvg s f x ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d := by
  unfold fullAvg
  rw [← integral_prod _ (mix_integrable s hf)]
  have h := integral_map (μ := (torusMeasure d).prod (torusMeasure d))
    (f := f) (φ := mix s) (mix_measurePreserving s).measurable.aemeasurable
    (by simpa only [(mix_measurePreserving s).map_eq] using hf.aestronglyMeasurable)
  rw [(mix_measurePreserving s).map_eq] at h
  exact h.symm

lemma fullAvg_nonneg {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : 0 ≤ᵐ[torusMeasure d] f) : 0 ≤ᵐ[torusMeasure d] fullAvg s f := by
  have h := (mix_measurePreserving s).quasiMeasurePreserving.ae hf
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  exact integral_nonneg_of_ae hx

lemma mix_eq_update {d : ℕ} (s : Finset (Fin d)) (x y : Torus d) :
    mix s (x,y) = updateFinset x s (s.restrict y) := by
  ext i
  simp [mix, updateFinset]

lemma fullAvg_eq_avg {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) : fullAvg s f = avg s f := by
  funext x
  let g : Torus d → ℝ := fun y => f (mix s (x,y))
  have hg : BoundedMeasurable g := by
    refine ⟨hf.1.comp ((mix_measurePreserving s).measurable.comp (measurable_const.prodMk measurable_id)), ?_⟩
    obtain ⟨B,hB⟩ := hf.2
    exact ⟨B,fun y => hB _⟩
  have he : avg s g = fun _ => avg s f x := by
    funext y
    simp only [avg, g, mix_eq_update, restrict_updateFinset]
  change (∫ y, g y ∂torusMeasure d) = _
  rw [← integral_avg s hg, he]
  simp

#print axioms mix_measurePreserving
#print axioms fullAvg_integrable
#print axioms integral_fullAvg
#print axioms fullAvg_nonneg
#print axioms fullAvg_eq_avg
end BecknerOnofri.HighDim.EntropyShearer

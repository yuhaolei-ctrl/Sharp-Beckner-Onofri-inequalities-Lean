module

public import BecknerOnofri.CoordinateRearrangementDefinitions
public import BecknerOnofri.CoordinateCircleProjection

@[expose] public section

/-! # Splitting off one coordinate of the torus (Fubini over a fiber)

For `i : Fin d` the map `fiberMap i : Torus d × Torus 1 → Torus d`, `(x, z) ↦ update x i (z 0)`,
is measure preserving for `m_d ⊗ m_1 → m_d`.  This is the measure-theoretic content of
"Fubini over the `i`-th circle fiber" used in the written proof of
`lem:coordinate-rearranged-minimizer`; the fiber of `f` over `x` is
`circleFiber i f x = fun z => f (fiberMap i (x, z))`. -/

noncomputable section
open MeasureTheory Set Function
open Legacy.TorusEndpoint BecknerOnofri.HighDim.CoordinateRearrangementStatement

namespace BecknerOnofri.V2.Rearrangement

/-- `(x, z) ↦ x` with its `i`-th coordinate replaced by the circle point `z 0`. -/
def fiberMap {d : ℕ} (i : Fin d) (p : Torus d × Torus 1) : Torus d :=
  Function.update p.1 i (p.2 0)

theorem fiberMap_measurable {d : ℕ} (i : Fin d) : Measurable (fiberMap i) := by
  unfold fiberMap
  exact (measurable_update' (a := i)).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))

theorem circleFiber_eq {d : ℕ} (i : Fin d) (f : Torus d → ℝ) (x : Torus d) :
    circleFiber i f x = fun z => f (fiberMap i (x, z)) := rfl

/-- The key Fubini fact: replacing coordinate `i` by an independent uniform circle point
preserves the Haar measure of the torus. -/
theorem fiberMap_measurePreserving {d : ℕ} (i : Fin d) :
    MeasurePreserving (fiberMap i) ((torusMeasure d).prod (torusMeasure 1)) (torusMeasure d) := by
  refine ⟨fiberMap_measurable i, ?_⟩
  have h1 : (torusMeasure 1) = Measure.pi (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
    torusMeasure_explicit 1
  have hd : (torusMeasure d) = Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
    torusMeasure_explicit d
  symm
  rw [hd]
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (fiberMap_measurable i) (MeasurableSet.univ_pi hs)]
  have hpre : fiberMap i ⁻¹' (Set.pi univ s) =
      (Set.pi univ (Function.update s i univ)) ×ˢ {z : Torus 1 | z 0 ∈ s i} := by
    ext ⟨x, z⟩
    simp only [fiberMap, mem_preimage, mem_pi, mem_univ, true_implies, mem_prod, mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j
        simpa [hj] using this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        simpa [hj] using this
  have hz : {z : Torus 1 | z 0 ∈ s i} = Set.pi univ (fun _ : Fin 1 => s i) := by
    ext z; simp
  rw [hpre, Measure.prod_prod, hz, h1, Measure.pi_pi, Measure.pi_pi]
  have hupd : (fun j => (AddCircle.haarAddCircle : Measure UnitAddCircle) (Function.update s i univ j)) =
      Function.update (fun j => (AddCircle.haarAddCircle : Measure UnitAddCircle) (s j)) i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [hupd]
  simp only [Finset.univ_unique, Finset.prod_singleton, Fin.default_eq_zero]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [one_mul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase, mul_comm]

section ProdSwap
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace D]

/-- `(A × B) × (C × D) → (A × C) × (B × D)` is measure preserving. -/
theorem measurePreserving_prodProdProdComm (μA : Measure A) (μB : Measure B) (μC : Measure C)
    (μD : Measure D) [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have g1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have g2 := (MeasurePreserving.id μA).prod
    (measurePreserving_prodAssoc μB μC μD).symm
  have g3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have g4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have g5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm
  have := g5.comp (g4.comp (g3.comp (g2.comp g1)))
  convert this using 1
  funext p
  rfl

end ProdSwap

/-- Two independent fiber replacements: `((x,y),(z,w)) ↦ (update x i (z 0), update y i (w 0))`. -/
def fiberMap₂ {d : ℕ} (i : Fin d) (p : (Torus d × Torus d) × (Torus 1 × Torus 1)) :
    Torus d × Torus d :=
  (fiberMap i (p.1.1, p.2.1), fiberMap i (p.1.2, p.2.2))

theorem fiberMap₂_measurePreserving {d : ℕ} (i : Fin d) :
    MeasurePreserving (fiberMap₂ i)
      (((torusMeasure d).prod (torusMeasure d)).prod ((torusMeasure 1).prod (torusMeasure 1)))
      ((torusMeasure d).prod (torusMeasure d)) := by
  have h := (fiberMap_measurePreserving i).prod (fiberMap_measurePreserving i)
  have hc := measurePreserving_prodProdProdComm (torusMeasure d) (torusMeasure d)
    (torusMeasure 1) (torusMeasure 1)
  exact h.comp hc

end BecknerOnofri.V2.Rearrangement

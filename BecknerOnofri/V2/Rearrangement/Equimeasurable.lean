module

public import BecknerOnofri.V2.Rearrangement.CoordinateSplit
public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import BecknerOnofri.V2.Vocab.HomEntropyIdent
public import BecknerOnofri.CircleRearrangementTrustedBridge
public import BecknerOnofri.CoordinateRearrangementDefinitions

@[expose] public section

/-! # Fiberwise equimeasurability preserves the distribution and the entropy

Manuscript `eq:coordinate-rearrangement-invariants`: if `r_i` is obtained from `r_{i-1}` by
symmetric decreasing rearrangement in coordinate `i`, then the fibers have equal distribution
functions, hence `‖r_i‖_∞ = ‖r_{i-1}‖_∞`, `r_i ∈ P_ac`, `Ent(r_i) = Ent(r_{i-1})`.  We prove the
global statement `IdentDistrib s r` from the fiberwise one (Fubini over `fiberMap`) and deduce the
sup bound and the entropy equality. -/

noncomputable section
open MeasureTheory Set ProbabilityTheory
open Legacy.TorusEndpoint BecknerOnofri.HighDim.CoordinateRearrangementStatement
open scoped ENNReal

namespace BecknerOnofri.V2.Rearrangement

variable {d : ℕ}

/-- Fibers of a.e. equal functions are a.e. equal, for a.e. base point. -/
theorem fibers_ae_of_ae_eq (i : Fin d) {f g : Torus d → ℝ} (h : f =ᵐ[torusMeasure d] g) :
    ∀ᵐ x ∂torusMeasure d, circleFiber i f x =ᵐ[torusMeasure 1] circleFiber i g x := by
  have := (fiberMap_measurePreserving (d := d) i).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod this

/-- The layer-cake rearrangement only depends on the a.e. class. -/
theorem rearrange_congr_ae {f g : Torus 1 → ℝ} (h : f =ᵐ[torusMeasure 1] g) :
    Circle.rearrange f = Circle.rearrange g := by
  funext x
  unfold Circle.rearrange
  have : ∀ t : ℝ, torusMeasure 1 {y | t < f y} = torusMeasure 1 {y | t < g y} := fun t =>
    measure_congr (h.mono fun y hy => by simp only [mem_ofPred_eq, hy])
  simp only [this]

theorem realRearrange_congr_ae {f g : Torus 1 → ℝ} (h : f =ᵐ[torusMeasure 1] g) :
    Circle.realRearrange f = Circle.realRearrange g := by
  unfold Circle.realRearrange
  rw [rearrange_congr_ae h]

/-- Fiberwise equidistribution from `AECanonicalStep`: a.e. fiber of `r`. -/
theorem fiber_identDistrib_of_step (i : Fin d) {r s : Torus d → ℝ}
    (hr : Integrable r (torusMeasure d)) (hr0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r x)
    (hstep : AECanonicalStep i r s) :
    ∀ᵐ x ∂torusMeasure d, ∀ B : Set ℝ, MeasurableSet B →
      torusMeasure 1 {z | s (fiberMap i (x, z)) ∈ B} = torusMeasure 1 {z | r (fiberMap i (x, z)) ∈ B} := by
  have hF := fiberMap_measurePreserving (d := d) i
  have hI : ∀ᵐ x ∂torusMeasure d, Integrable (circleFiber i r x) (torusMeasure 1) :=
    (hF.integrable_comp_of_integrable hr).prod_right_ae
  have hN : ∀ᵐ x ∂torusMeasure d, ∀ᵐ z ∂torusMeasure 1, 0 ≤ circleFiber i r x z :=
    Measure.ae_ae_of_ae_prod (hF.quasiMeasurePreserving.ae hr0)
  filter_upwards [hI, hN, hstep] with x h1 h2 h3 B hB
  obtain ⟨-, -, -, -, hid, -⟩ := Circle.circle_rearrangement (circleFiber i r x) (circleFiber i r x)
    h1 h1 h2 h2 (fun _ => 0) (C := 0) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ _ _ => le_rfl)
  have e1 := hid.measure_mem_eq hB
  have e2 : torusMeasure 1 (Circle.realRearrange (circleFiber i r x) ⁻¹' B) =
      torusMeasure 1 (circleFiber i s x ⁻¹' B) :=
    measure_congr (h3.mono fun z hz => by simp only [mem_preimage, hz])
  rw [e2] at e1
  exact e1

/-- **Fiberwise rearrangement is equimeasurable.**  If `s` is the canonical circle rearrangement
of `r` in coordinate `i` (a.e. fiber), then `s` and `r` have the same distribution on the torus. -/
theorem step_identDistrib (i : Fin d) {r s : Torus d → ℝ}
    (hr : Integrable r (torusMeasure d)) (hr0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r x)
    (hs : AEStronglyMeasurable s (torusMeasure d)) (hstep : AECanonicalStep i r s) :
    IdentDistrib s r (torusMeasure d) (torusMeasure d) := by
  have hF := fiberMap_measurePreserving (d := d) i
  -- measurable representatives
  set r' := hr.1.mk r with hr'
  set s' := hs.mk s with hs'
  have hrr : r =ᵐ[torusMeasure d] r' := hr.1.ae_eq_mk
  have hss : s =ᵐ[torusMeasure d] s' := hs.ae_eq_mk
  have hr'm : Measurable r' := hr.1.stronglyMeasurable_mk.measurable
  have hs'm : Measurable s' := hs.stronglyMeasurable_mk.measurable
  have hr'i : Integrable r' (torusMeasure d) := hr.congr hrr
  have hr'0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r' x := by
    filter_upwards [hr0, hrr] with x h1 h2
    rwa [← h2]
  have hstep' : AECanonicalStep i r' s' := by
    unfold AECanonicalStep at hstep ⊢
    filter_upwards [hstep, fibers_ae_of_ae_eq i hrr, fibers_ae_of_ae_eq i hss] with x h1 h2 h3
    rw [← realRearrange_congr_ae h2]
    exact h1.trans h3
  have key := fiber_identDistrib_of_step i hr'i hr'0 hstep'
  have hmeas : ∀ B : Set ℝ, MeasurableSet B →
      torusMeasure d (s' ⁻¹' B) = torusMeasure d (r' ⁻¹' B) := by
    intro B hB
    have h1 : MeasurableSet (fiberMap i ⁻¹' (s' ⁻¹' B)) := (fiberMap_measurable i) (hs'm hB)
    have h2 : MeasurableSet (fiberMap i ⁻¹' (r' ⁻¹' B)) := (fiberMap_measurable i) (hr'm hB)
    rw [← hF.measure_preimage (hs'm hB).nullMeasurableSet,
      ← hF.measure_preimage (hr'm hB).nullMeasurableSet,
      Measure.prod_apply h1, Measure.prod_apply h2]
    refine lintegral_congr_ae ?_
    filter_upwards [key] with x hx
    exact hx B hB
  have hid : IdentDistrib s' r' (torusMeasure d) (torusMeasure d) := by
    refine ⟨hs'm.aemeasurable, hr'm.aemeasurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hs'm hB, Measure.map_apply hr'm hB]
    exact hmeas B hB
  refine ⟨hs.aemeasurable, hr.1.aemeasurable, ?_⟩
  rw [Measure.map_congr hss, Measure.map_congr hrr]
  exact hid.map_eq

/-- The sup bound survives rearrangement (`‖r_i‖_∞ = ‖r_{i-1}‖_∞`, in the form `r ≤ M ⇒ s ≤ M`). -/
theorem step_ae_le (i : Fin d) {r s : Torus d → ℝ} {M : ℝ}
    (hr : Integrable r (torusMeasure d)) (hr0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r x)
    (hs : AEStronglyMeasurable s (torusMeasure d)) (hstep : AECanonicalStep i r s)
    (hM : ∀ᵐ x ∂torusMeasure d, r x ≤ M) : ∀ᵐ x ∂torusMeasure d, s x ≤ M := by
  have hid := step_identDistrib i hr hr0 hs hstep
  have e := hid.measure_mem_eq (measurableSet_Ioi (a := M))
  have h0 : torusMeasure d {x | ¬ r x ≤ M} = 0 := ae_iff.mp hM
  have h1 : {x | ¬ s x ≤ M} = s ⁻¹' Ioi M := by ext x; simp
  have h2 : {x | ¬ r x ≤ M} = r ⁻¹' Ioi M := by ext x; simp
  exact ae_iff.mpr (by rw [h1, e, ← h2, h0])

/-- Mass, integrability and nonnegativity survive rearrangement. -/
theorem step_integrable (i : Fin d) {r s : Torus d → ℝ}
    (hr : Integrable r (torusMeasure d)) (hr0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r x)
    (hs : AEStronglyMeasurable s (torusMeasure d)) (hstep : AECanonicalStep i r s) :
    Integrable s (torusMeasure d) ∧ (∀ᵐ x ∂torusMeasure d, 0 ≤ s x) ∧
      ∫ x, s x ∂torusMeasure d = ∫ x, r x ∂torusMeasure d := by
  have hid := step_identDistrib i hr hr0 hs hstep
  refine ⟨?_, ?_, hid.integral_eq⟩
  · exact hid.integrable_iff.mpr hr
  · have e := hid.measure_mem_eq (measurableSet_Iio (a := (0 : ℝ)))
    have h0 : torusMeasure d {x | ¬ 0 ≤ r x} = 0 := ae_iff.mp hr0
    have h1 : {x | ¬ 0 ≤ s x} = s ⁻¹' Iio 0 := by ext x; simp
    have h2 : {x | ¬ 0 ≤ r x} = r ⁻¹' Iio 0 := by ext x; simp
    exact ae_iff.mpr (by rw [h1, e, ← h2, h0])

/-- Entropy is unchanged by a fiberwise rearrangement (`Ent(r_i) = Ent(r_{i-1})`). -/
theorem step_homEntropy_eq (i : Fin d) {r s : Torus d → ℝ}
    (hr : Integrable r (torusMeasure d)) (hr0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ r x)
    (hs : AEStronglyMeasurable s (torusMeasure d)) (hstep : AECanonicalStep i r s) :
    BecknerOnofri.V2.Vocab.homEntropy (torusMeasure d) s =
      BecknerOnofri.V2.Vocab.homEntropy (torusMeasure d) r :=
  BecknerOnofri.V2.Vocab.homEntropy_identDistrib (step_identDistrib i hr hr0 hs hstep)

end BecknerOnofri.V2.Rearrangement

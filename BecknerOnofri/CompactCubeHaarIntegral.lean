import BecknerOnofri.SmoothCompactParameterIntegral
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Fourier.AddCircle

/-! Haar integration as integration over the compact unit cube; endpoints
have zero measure, so the closed cube is available for differentiation. -/
noncomputable section
open MeasureTheory Set
open scoped unitInterval ContDiff
namespace BecknerOnofri.CompactParameter
abbrev UnitCircle := AddCircle (1 : ℝ)

lemma unitInterval_circle_preserving :
    MeasurePreserving (fun y : I => ((y : ℝ) : UnitCircle)) volume AddCircle.haarAddCircle := by
  have h := AddCircle.measurePreserving_mk (T := 1) (0 : ℝ)
  have hv : (volume : Measure UnitCircle)=AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T := 1)
  rw [zero_add,restrict_Ioc_eq_restrict_Icc,hv] at h
  exact h.comp unitInterval.measurePreserving_coe

lemma unitCube_circle_preserving {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun y : ι → I => fun j => ((y j : ℝ) : UnitCircle))
      (Measure.pi (fun _ : ι => (volume : Measure I)))
      (Measure.pi (fun _ : ι => (AddCircle.haarAddCircle : Measure UnitCircle))) :=
  measurePreserving_pi _ _ (fun _ => unitInterval_circle_preserving)

lemma integral_circle_eq_cube {ι : Type*} [Fintype ι]
    (G : (ι → UnitCircle) → ℝ) (hG : Continuous G) :
    (∫ x,G x ∂Measure.pi (fun _ : ι => (AddCircle.haarAddCircle : Measure UnitCircle)))=
      ∫ y : ι → I,G (fun j => ((y j : ℝ) : UnitCircle))
        ∂Measure.pi (fun _ : ι => (volume : Measure I)) := by
  have h := unitCube_circle_preserving (ι := ι)
  rw [← h.map_eq]
  exact integral_map_of_stronglyMeasurable h.measurable hG.stronglyMeasurable

/-- A smooth periodic lift suffices to differentiate the actual Haar integral. -/
theorem haar_parameter_contDiff {ι : Type*} [Fintype ι]
    (G : ℝ → (ι → UnitCircle) → ℝ) (hG : ∀ t,Continuous (G t))
    (F : ℝ × (ι → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (he : ∀ t y,F (t,y)=G t (fun j => (y j : UnitCircle))) :
    ContDiff ℝ ∞ (fun t => ∫ x,G t x
      ∂Measure.pi (fun _ : ι => (AddCircle.haarAddCircle : Measure UnitCircle))) := by
  have h := integral_contDiff_of_compact_parameter
    (Measure.pi (fun _ : ι => (volume : Measure I)))
    (fun y : ι → I => fun j => (y j : ℝ)) (by fun_prop) F hF
  have heq : (fun t => ∫ x,G t x
      ∂Measure.pi (fun _ : ι => (AddCircle.haarAddCircle : Measure UnitCircle)))=
      (fun t => ∫ y : ι → I,F (t,fun j => (y j : ℝ))
        ∂Measure.pi (fun _ : ι => (volume : Measure I))) := by
    funext t
    rw [integral_circle_eq_cube (G t) (hG t)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => (he t _).symm))
  rw [heq]
  exact h

#print axioms unitInterval_circle_preserving
#print axioms haar_parameter_contDiff
end BecknerOnofri.CompactParameter

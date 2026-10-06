module

public import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

def coordinateLength (m : ℕ) : ℝ := if m=0 then 2*Real.pi else Real.pi

def openBox {d : ℕ} (α : MultiIndex d) : Set (Space d) :=
  Set.univ.pi (fun i => Ioo 0 (coordinateLength (α i)))

lemma coordinateLength_pos (m : ℕ) : 0<coordinateLength m := by
  unfold coordinateLength
  split_ifs <;> positivity

lemma coordinateMeasure_open (m : ℕ) :
    coordinateMeasure m=volume.restrict (Ioo 0 (coordinateLength m)) := by
  unfold coordinateMeasure coordinateLength
  split_ifs
  · exact restrict_Ioo_eq_restrict_Ioc.symm
  · rfl

lemma isOpen_openBox {d : ℕ} (α : MultiIndex d) : IsOpen (openBox α) :=
  isOpen_set_pi Set.finite_univ (fun i hi => isOpen_Ioo)

lemma spatialMeasure_openBox {d : ℕ} (α : MultiIndex d) :
    spatialMeasure α=volume.restrict (openBox α) := by
  unfold spatialMeasure openBox
  simp_rw [coordinateMeasure_open]
  rw [← Measure.restrict_pi_pi]
  rfl

lemma ae_mem_openBox {d : ℕ} (α : MultiIndex d) : ∀ᵐ x ∂spatialMeasure α,x∈openBox α := by
  rw [spatialMeasure_openBox]
  exact ae_restrict_mem (isOpen_openBox α).measurableSet

lemma partialDerivative_continuous {d : ℕ} {F : Space d → ℝ}
    (hF : ContDiff ℝ ∞ F) (i : Fin d) : Continuous (partialDerivative i F) :=
  (hF.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)

lemma supported_fiber_endpoints {d : ℕ} {α : MultiIndex d} {ψ : Space d → ℝ}
    (hψ : tsupport ψ ⊆ openBox α) (x : Space d) (i : Fin d) :
    ψ (Function.update x i 0)=0 ∧ ψ (Function.update x i (coordinateLength (α i)))=0 := by
  constructor
  · by_contra hn
    have ht := hψ (subset_closure (show Function.update x i 0∈Function.support ψ from hn))
    have hh := ht i (Set.mem_univ i)
    simpa using hh.1
  · by_contra hn
    have ht := hψ (subset_closure (show Function.update x i (coordinateLength (α i))∈Function.support ψ from hn))
    have hh := ht i (Set.mem_univ i)
    simpa using hh.2

#print axioms spatialMeasure_openBox
end BecknerOnofri.Friedrichs.MixedSpatial

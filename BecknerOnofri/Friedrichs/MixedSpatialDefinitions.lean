module

public import BecknerOnofri.Friedrichs.SpatialFormDefinitions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

/-! Actual mixed spatial form data. Inactive coordinates retain their full
2*pi period; they are not replaced by Neumann half intervals. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev MultiIndex (d : ℕ) := Fin d → ℕ

def coordinateMeasure (m : ℕ) : Measure ℝ :=
  if m=0 then volume.restrict (Ioc 0 (2*Real.pi)) else volume.restrict (Ioo 0 Real.pi)

instance (m : ℕ) : IsFiniteMeasure (coordinateMeasure m) := by
  unfold coordinateMeasure
  split_ifs <;> infer_instance

def spatialMeasure {d : ℕ} (α : MultiIndex d) : Measure (Space d) :=
  Measure.pi (fun i => coordinateMeasure (α i))

instance {d : ℕ} (α : MultiIndex d) : IsFiniteMeasure (spatialMeasure α) := by
  unfold spatialMeasure
  infer_instance

abbrev H {d : ℕ} (α : MultiIndex d) := Lp ℝ 2 (spatialMeasure α)
abbrev EnergySpace {d : ℕ} (α : MultiIndex d) := H α × ((Fin d → H α) × (Fin d → H α))

def inactivePeriodic {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ) : Prop :=
  ∀ i,α i=0 → ∀ x,F (Function.update x i (x i+2*Real.pi))=F x

def interiorSupport {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ) : Prop :=
  ∃ δ : ℝ,0<δ ∧ ∀ x, (∃ i,0<α i ∧ (x i≤δ ∨ Real.pi-δ≤x i)) → F x=0

def smoothCoreProfile {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ inactivePeriodic α F ∧ interiorSupport α F

def partialDerivative {d : ℕ} (i : Fin d) (F : Space d → ℝ) (x : Space d) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

def core {d : ℕ} (α : MultiIndex d) : Set (EnergySpace α) :=
  {v | ∃ F : Space d → ℝ,smoothCoreProfile α F ∧
    (v.1 : Space d → ℝ)=ᵐ[spatialMeasure α] F ∧
    (∀ i,(v.2.1 i : Space d → ℝ)=ᵐ[spatialMeasure α] partialDerivative i F) ∧
    (∀ i,(v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => SpatialForm.potentialFactor (α i) (x i)*F x))}

def formClosure {d : ℕ} (α : MultiIndex d) : Set (EnergySpace α) := closure (core α)

def formPairing {d : ℕ} {α : MultiIndex d} (v w : EnergySpace α) : ℝ :=
  ∑ i,(inner ℝ (v.2.1 i) (w.2.1 i)+inner ℝ (v.2.2 i) (w.2.2 i))

def operatorGraph {d : ℕ} (α : MultiIndex d) (f g : H α) : Prop :=
  ∃ v : EnergySpace α,v.1=f ∧ v∈formClosure α ∧
    ∀ w∈formClosure α,formPairing v w=inner ℝ g w.1

end BecknerOnofri.Friedrichs.MixedSpatial

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Spatial form closure, defined independently of the Jacobi spectrum.
A core element records the function, its actual derivative, and its actual
singular potential weight in L2(0,pi). The graph relation tests the closed
form against smooth compactly supported functions. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm

def intervalMeasure : Measure ℝ := volume.restrict (Ioo 0 Real.pi)
abbrev H := Lp ℝ 2 intervalMeasure
abbrev EnergySpace := H × (H × H)

def potentialFactor (m : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt ((m:ℝ)*((m:ℝ)-1))/Real.sin t

def core (m : ℕ) : Set EnergySpace :=
  {v | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 Real.pi ∧
    (v.1 : ℝ → ℝ)=ᵐ[intervalMeasure] φ ∧
    (v.2.1 : ℝ → ℝ)=ᵐ[intervalMeasure] deriv φ ∧
    (v.2.2 : ℝ → ℝ)=ᵐ[intervalMeasure] (fun t => potentialFactor m t*φ t)}

def formClosure (m : ℕ) : Set EnergySpace := closure (core m)

def operatorGraph (m : ℕ) (f g : H) : Prop :=
  ∃ p v : H, (f,(p,v))∈formClosure m ∧
    ∀ w∈core m, inner ℝ p w.2.1+inner ℝ v w.2.2=inner ℝ g w.1

end BecknerOnofri.Friedrichs.SpatialForm

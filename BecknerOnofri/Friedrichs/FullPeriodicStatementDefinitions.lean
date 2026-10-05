import BecknerOnofri.Friedrichs.MixedEigenStatementDefinitions
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Trusted explicit auxiliary statements for the full periodic sectors.
These statements assert actual functions, measures and spatial graphs. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def FullSpatialEigenvectors (d : ℕ) : Prop :=
  ∀ (α n : MultiIndex d) (odd : Fin d → Bool),∃ v : H α,
    (v : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => ∏ i,if α i=0 then
        (if odd i then Real.sin ((n i:ℝ)*x i) else Real.cos ((n i:ℝ)*x i)) else
        Real.sin (x i)^(α i)*
          (Polynomial.derivative^[α i] (Polynomial.Chebyshev.T ℝ (n i:ℤ))).eval (Real.cos (x i))) ∧
      operatorGraph α v ((∑ i,(n i:ℝ)^2) • v)

def FullCoordinateTotality : Prop :=
  ∀ (m : ℕ) (f : Lp ℝ 2 (coordinateMeasure m)),
    (∀ (odd : Bool) (n : ℕ),
      (∫ t,(if m=0 then (if odd then Real.sin ((n:ℝ)*t) else Real.cos ((n:ℝ)*t)) else
        Real.sin t^m*(Polynomial.derivative^[m] (Polynomial.Chebyshev.T ℝ (n:ℤ))).eval (Real.cos t))*f t
        ∂coordinateMeasure m)=0) → f=0

def FullPeriodicHilbertBasis : Prop :=
  ∃ b : HilbertBasis (ℕ ⊕ ℕ) ℝ (Lp ℝ 2 (volume.restrict (Ioc 0 (2*Real.pi)))),
    (∀ n : ℕ,(b (Sum.inl n) : ℝ → ℝ)=ᵐ[volume.restrict (Ioc 0 (2*Real.pi))]
      (fun t => (Real.sqrt (if n=0 then 2*Real.pi else Real.pi))⁻¹*Real.cos ((n:ℝ)*t))) ∧
    (∀ n : ℕ,(b (Sum.inr n) : ℝ → ℝ)=ᵐ[volume.restrict (Ioc 0 (2*Real.pi))]
      (fun t => (Real.sqrt Real.pi)⁻¹*Real.sin (((n+1:ℕ):ℝ)*t)))

end BecknerOnofri.Friedrichs.MixedSpatial

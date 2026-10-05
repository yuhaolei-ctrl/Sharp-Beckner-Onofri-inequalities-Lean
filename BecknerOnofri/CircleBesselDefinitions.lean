module

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! The exact positive-series special functions appearing in the source.
No numerical enclosure or derivative property is included in these definitions. -/
namespace BecknerOnofri.HighDim.CircleScalar
noncomputable def bessel (n : ℕ) (h : ℝ) : ℝ :=
  ∑' j : ℕ, h^(2*j+n)/((j.factorial:ℝ)*(j+n).factorial)
noncomputable def besselMoment (n : ℕ) (h : ℝ) : ℝ := bessel n h/bessel 0 h
end BecknerOnofri.HighDim.CircleScalar

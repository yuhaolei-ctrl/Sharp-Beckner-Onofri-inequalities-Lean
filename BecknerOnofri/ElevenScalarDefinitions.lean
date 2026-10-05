import BecknerOnofri.EntropyTailDefinitions

/-! The full scalar lattice energy G_{11,n} in Section 4. The origin is
explicitly removed, and the Euclidean squared radius is a sum of squares.
There are no certificate, regularity, or inequality premises in this file. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Eleven
def scalarEnergy (n : ℕ) : ℝ :=
  ∑' k : Frequency 11,
    (if k = 0 then 0 else 1 / Real.sqrt ((∑ i : Fin 11, (k i : ℝ)^2)^11)) *
      ∏ i : Fin 11, EntropyTail.scalarCoefficient n (k i).natAbs
end BecknerOnofri.HighDim.Eleven

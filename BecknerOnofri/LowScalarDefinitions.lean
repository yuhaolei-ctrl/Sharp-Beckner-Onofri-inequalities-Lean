import BecknerOnofri.EntropyTailDefinitions

/-! Literal scalar lattice and hypergeometric quantities from Section 3. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.LowScalar

def energy (d n : ℕ) : ℝ :=
  ∑' k : Frequency d,
    (if k = 0 then 0 else 1 / Real.sqrt ((∑ i : Fin d, (k i : ℝ)^2)^d)) *
      ∏ i : Fin d, EntropyTail.scalarCoefficient n (k i).natAbs

def mixingWeight (n m l : ℕ) : ℝ :=
  ((n.choose l : ℝ)*(m.choose l : ℝ))/((n+m).choose n : ℝ)

def theta (t : ℝ) : ℝ := ∑' j : ℤ, Real.exp (-t*(j:ℝ)^2)

def thetaIntegral (d : ℕ) : ℝ :=
  ∫ r : ℝ in Set.Ici 1,
    (r^((d:ℝ)/2-1)+r⁻¹)*(theta (Real.pi*r)^d-1)

end BecknerOnofri.HighDim.LowScalar

import BecknerOnofri.ClosedCubeTaylorDefinitions
import Legacy.BecknerOnofri.BernsteinPositiveCoefficients

noncomputable section
open scoped BigOperators Topology ContDiff
namespace BecknerOnofri.HighDim.ClosedCubeTaylor
open Legacy.BecknerOnofri.BernsteinPositiveCoefficients

theorem closed_cube_expansion {d : ℕ} (f : Space d → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Icc (0 : Space d) 1))
    (hpos : nonnegativePartials f) :
    (∀ a, 0 ≤ coefficient f a) ∧ HasSum (coefficient f) (f 1) ∧
    (∀ y : Cube d, HasSum (fun a => coefficient f a * monomial a y)
      (f (fun i => (y i : ℝ)))) ∧
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, coefficient f a * monomial a y)
      (fun y => f (fun i => (y i : ℝ))) Filter.atTop := by
  exact ⟨taylorCoefficient_nonneg hpos, positiveTaylor_mass hf hpos,
    positiveTaylor_hasSum hf hpos, positiveTaylor_uniform hf hpos⟩

#print axioms closed_cube_expansion
end BecknerOnofri.HighDim.ClosedCubeTaylor

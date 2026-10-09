module

public import BecknerOnofri.V2.FiniteState.FamilyVariance

@[expose] public section

/-!
# Fair-spin orthogonality of the symmetric features, `A_1 = x`, `A_2 = (12 x² - 1)/11`
(`d12-spin-eq:orthogonal`, `d12-spin-eq:A2`; Appendix A.3 "Behavior at zero").

ROUTE DIFFERENCE.  The manuscript proves the orthogonality relations by expanding both averages
over subsets of spins.  Here the same finite statements are kernel-checked rational identities
(`decide +kernel`) for the concrete thirteen-state data `referenceQ`, `momentQ`, `meanCoordinateQ`;
they are then cast to `ℝ`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

theorem momentQ_one : ∀ j : Count, momentQ ⟨0, by decide⟩ j = meanCoordinateQ j := by
  decide +kernel

theorem momentQ_two : ∀ j : Count,
    momentQ ⟨1, by decide⟩ j = (12 * meanCoordinateQ j ^ 2 - 1) / 11 := by
  decide +kernel

theorem referenceQ_moment_zero : ∀ s : Order, ∑ j : Count, referenceQ j * momentQ s j = 0 := by
  decide +kernel

theorem referenceQ_moment_orthogonal : ∀ s r : Order,
    ∑ j : Count, referenceQ j * (momentQ s j * momentQ r j) =
      if s = r then 1 / ((12 : ℕ).choose (s.val + 1) : ℚ) else 0 := by
  decide +kernel

/-- `A_{1,j} = x_j`. -/
theorem moment_one (j : Count) : moment ⟨0, by decide⟩ j = meanCoordinate j := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (momentQ_one j)
  simpa [moment, meanCoordinate] using h

/-- `A_{2,j} = (12 x_j² - 1)/11`. -/
theorem moment_two (j : Count) :
    moment ⟨1, by decide⟩ j = (12 * meanCoordinate j ^ 2 - 1) / 11 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (momentQ_two j)
  simpa [moment, meanCoordinate] using h

/-- `∑_j b_j A_{s,j} = 0`. -/
theorem reference_moment_zero (s : Order) : ∑ j : Count, reference j * moment s j = 0 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (referenceQ_moment_zero s)
  simpa [moment, reference] using h

/-- `∑_j b_j A_{s,j} A_{r,j} = δ_{sr} / C(12,s)` (orders encoded as `s.val + 1`). -/
theorem reference_moment_orthogonal (s r : Order) :
    ∑ j : Count, reference j * (moment s j * moment r j) =
      if s = r then 1 / ((12 : ℕ).choose (s.val + 1) : ℝ) else 0 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (referenceQ_moment_orthogonal s r)
  by_cases hsr : s = r
  · simpa [moment, reference, hsr] using h
  · simpa [moment, reference, hsr] using h

end BecknerOnofri.V2.FiniteState

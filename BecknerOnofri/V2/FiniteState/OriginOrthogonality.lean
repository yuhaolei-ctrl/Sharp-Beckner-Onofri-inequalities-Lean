module

public import BecknerOnofri.V2.FiniteState.FamilyVariance
public import BecknerOnofri.V2.Reaudit.ScalarBridges.KrawtchoukOrthogonality

@[expose] public section

/-!
# Fair-spin orthogonality of the symmetric features, `A_1 = x`, `A_2 = (12 x² - 1)/11`
(`d12-spin-eq:orthogonal`, `d12-spin-eq:A2`; Appendix A.3 "Behavior at zero").

The manuscript proves the orthogonality relations by expanding both averages over subsets of
independent fair spins.  The proofs below are exactly that argument
(`V2.Reaudit.ScalarBridges.KrawtchoukOrthogonality`: independence and orthogonality of the spin
products, the Krawtchouk generating function, Newton's identity, double counting).  The earlier
kernel-evaluated rational identities for the thirteen-state data (`decide +kernel`) have been removed.
-/

noncomputable section
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- `A_{1,j} = x_j`. -/
theorem moment_one (j : Count) : moment ⟨0, by decide⟩ j = meanCoordinate j :=
  Reaudit.ScalarBridges.moment_one_spins j

/-- `A_{2,j} = (12 x_j² - 1)/11`. -/
theorem moment_two (j : Count) :
    moment ⟨1, by decide⟩ j = (12 * meanCoordinate j ^ 2 - 1) / 11 :=
  Reaudit.ScalarBridges.moment_two_spins j

/-- `∑_j b_j A_{s,j} = 0`. -/
theorem reference_moment_zero (s : Order) : ∑ j : Count, reference j * moment s j = 0 :=
  Reaudit.ScalarBridges.reference_moment_zero_spins s

/-- `∑_j b_j A_{s,j} A_{r,j} = δ_{sr} / C(12,s)` (orders encoded as `s.val + 1`). -/
theorem reference_moment_orthogonal (s r : Order) :
    ∑ j : Count, reference j * (moment s j * moment r j) =
      if s = r then 1 / ((12 : ℕ).choose (s.val + 1) : ℝ) else 0 :=
  Reaudit.ScalarBridges.reference_moment_orthogonal_spins s r

end BecknerOnofri.V2.FiniteState

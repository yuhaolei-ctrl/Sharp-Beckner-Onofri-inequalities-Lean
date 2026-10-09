module

public import BecknerOnofri.SpinDefinitions
public import Mathlib.Tactic

@[expose] public section

/-!
# Rational certificate of Appendix B.3 (`eq:section5-affine-residual-bounds`)

Compiled (sorry-free).  Adapted from the handoff's draft_lean/AffineCertificate.lean;
the coefficient tables are `List.getD` lookups instead of `![...]` so that kernel
reduction (`decide +kernel`) does not depend on `Matrix.vecCons`.  Order `s : Order = Fin 12`
encodes the manuscript order `s.val + 1`; `10 α_s`, `10 β_s`, `u_j` are exactly the printed rows.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

def alphaQ (s : Order) : ℚ :=
  ([0, 5, -2, 2, 0, 1, 2, 0, 3, -3, 0, 0] : List ℚ).getD s.val 0 / 10

def betaQ (s : Order) : ℚ :=
  ([10, 2, 8, 4, 6, 5, 4, 7, 2, 10, 0, 0] : List ℚ).getD s.val 0 / 10

/-- The printed bounds `u_j / 1000`. -/
def upperQ (j : Count) : ℚ :=
  ([5064, 837, 709, 694, 740, 795, 835, 870, 890, 880, 853, 867, 893] : List ℚ).getD j.val 0 / 1000

/-- `∑_s w_s (A_{s,j} - α_s - β_s x_j)^2`, with `A_{s,j} = momentQ s j`, `w_s = weightQ s`. -/
def residualQ (j : Count) : ℚ :=
  ∑ s : Order, weightQ s * (momentQ s j - alphaQ s - betaQ s * meanCoordinateQ j) ^ 2

theorem residualQ_lt_upperQ : ∀ j : Count, residualQ j < upperQ j := by
  decide +kernel

/-- "less than 6 at `j = 0` and less than 179/200 at every other state". -/
theorem upperQ_le_cap : ∀ j : Count, upperQ j ≤ (if j = 0 then (6 : ℚ) else 179 / 200) := by
  decide +kernel

theorem residualQ_lt_cap (j : Count) : residualQ j < (if j = 0 then (6 : ℚ) else 179 / 200) :=
  (residualQ_lt_upperQ j).trans_le (upperQ_le_cap j)

theorem curvature_coefficient_identity : (179 / 200 : ℚ) + 6 / 4096 = 45899 / 51200 := by
  norm_num

theorem curvature_coefficient_lt : (45899 / 51200 : ℚ) < 9 / 10 := by norm_num

end BecknerOnofri.V2.FiniteState

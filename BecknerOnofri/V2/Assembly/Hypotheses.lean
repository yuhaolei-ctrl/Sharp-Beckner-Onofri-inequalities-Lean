module

public import BecknerOnofri.V2.FiniteState.FamilyComparison

@[expose] public section

/-!
# Named hypotheses of the d = 12 assembly (work package G14)

Each declaration here is a `Prop` whose content is exactly the printed statement of a result that is
proved in another work package and is NOT yet available in the v2 worktree.  Nothing stronger is
assumed; the unused-by-the-proof clauses of the printed statements are kept.

* `ScalarBounds` : `d12-spin-lem:scalar` (Lemma 5.21; G13), the three computer-assisted scalar
  bounds for the explicit reference family, on the complete interval `0 ≤ t ≤ 99/100`.
-/

noncomputable section
namespace BecknerOnofri.V2.Assembly
open BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-- **Lemma 5.21 (`d12-spin-lem:scalar`, `d12-spin-eq:three`), as printed.**
For the explicit family `p(t)` (`famLaw`) and the residual `e_j(t)` (`famResid`),
`f(t) ≥ t⁴/10` (strict for `t > 0`), `𝒱(t) ≤ t⁴/50`, and `e_j(t) ≥ -1/4` for `0 ≤ j ≤ 12`,
for all `0 ≤ t ≤ 99/100`. -/
def ScalarBounds : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 99 / 100 →
    (t ^ 4 / 10 ≤ famF t ∧ (0 < t → t ^ 4 / 10 < famF t)) ∧
    famResidVar t ≤ t ^ 4 / 50 ∧
    ∀ j : Count, -(1 / 4 : ℝ) ≤ famResid t j

end BecknerOnofri.V2.Assembly
